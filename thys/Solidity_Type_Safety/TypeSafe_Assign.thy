section \<open>Preservation for assignments\<close>

theory TypeSafe_Assign
  imports TypeSafe_Statement_Support
begin

context typesafe_base
begin

text \<open>Each lemma covers one case of the parent's @{thm [source] assign}
  rule for \<open>ASSIGN\<close>, distinguished by the kinds of the assigned value and
  of the target location. Together they give the \<open>ASSIGN\<close> case of
  @{text TypeSafe_Statements}.\<close>

text \<open>Assignment case 1: a value assigned to a stack variable.\<close>

lemma TypeSafe_Assign_1:
  assumes "TypeSafe env (Accounts st) (Stack st) (Memory st) (Storage st) cd"
    and "stmt (ASSIGN lv ex) env cd st = Normal ((), st')"
    and "fullyInitialised env (Accounts st) (Stack st)"
    and "expr ex env cd (st\<lparr>state.Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>) (state.Gas st - costs (ASSIGN lv ex) env cd st) = Normal ((KValue v, Value t2), g)"
    and "lexp lv env cd (st\<lparr>state.Gas := g\<rparr>) g = Normal((LStackloc l2, Value t'),g')"
    and "convert t2 t' v = Some v'"
    and "st' = st\<lparr>state.Gas := g', Stack := updateStore l2 (KValue v') (Stack st)\<rparr>"
  shows "StateInvariant env st st' cd"
proof -
  let ?case = "StateInvariant env st st' cd"
  note 2 = assms(1-3)
  note 1 = assms(4-7)
  show "StateInvariant env st st' cd" unfolding StateInvariant_def TypeSafe_def
  proof (intros)
    show "typeCompat (Denvalue env) (Stack st') (Memory st') (Storage st' (Address env)) cd" unfolding typeCompat_def
    proof intros
      fix t l assume a10:"(t, l) |\<in>| fmran (Denvalue env)"
      show "denvalueCon (Stack st') (Memory st') (Storage st' (Address env)) cd t l"
      proof (split denvalue.split, intros)
        fix loc assume a20:"l = Stackloc loc"
        show "case accessStore loc (Stack st') of None \<Rightarrow> False
              | Some (KValue val) \<Rightarrow> (case t of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
              | Some (KCDptr stloc) \<Rightarrow> (case t of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
              | Some (KMemptr stloc) \<Rightarrow> (case t of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
              | Some (KStoptr stloc) \<Rightarrow> (case t of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address env)) | _ \<Rightarrow> False)"
        proof (cases "loc = l2")
          case False
          show ?thesis
          proof (split option.split, intros)
            assume a30:"accessStore loc (Stack st') = None"
            then have "accessStore loc (Stack st) = None" using 1(4) False by (simp add:stackSingleUpdate)
            then show False using a30 a20 a10 assms False 2(1) unfolding TypeSafe_def typeCompat_def by force
          next
            fix x2 assume a30:"accessStore loc (Stack st') = Some x2"
            then have a40:"accessStore loc (Stack st) = Some x2" using 1(4) False by (simp add:stackSingleUpdate)
            then have a50:"(Memory st) = (Memory st')" using 1(4) by simp
            then have a60:"(Storage st) = (Storage st')" using 1(4) by simp
            show "case x2 of KValue val \<Rightarrow> (case t of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
                  | KCDptr stloc \<Rightarrow> (case t of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
                  | KMemptr stloc \<Rightarrow> (case t of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
                  | KStoptr stloc \<Rightarrow> (case t of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address env)) | _ \<Rightarrow> False)"
              using a10 a20 a30 a40 a50 a60 2(1) unfolding TypeSafe_def typeCompat_def by (cases x2; cases t; force)
          qed
        next
          case sameLoc:True
          show ?thesis
          proof (split option.split, intros)
            assume a30:"accessStore loc (Stack st') = None"
            then show False using a20 a10 assms(1) sameLoc 1(4) notNoneUpdate[of st' g' loc "KValue v'" ] by simp
          next
            fix x2 assume a30:"accessStore loc (Stack st') = Some x2"
            show "case x2 of KValue val \<Rightarrow> (case t of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
              | KCDptr stloc \<Rightarrow> (case t of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
              | KMemptr stloc \<Rightarrow> (case t of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
              | KStoptr stloc \<Rightarrow> (case t of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address env)) | _ \<Rightarrow> False)"
            proof(cases "x2")
              case (KValue x1)
              then have a40:"unique_locations (Denvalue env)" using 2(1) typeSafeUnique by simp
              then have "(Value t', l2) = (t, loc)" using a40 a20 1(2) lexpStackloc_imps_inDen a10 sameLoc
                  uniqueLocs[of env "(t,l)" "(Value t', Stackloc l2)"] by simp
              then have True:"Value t' = t" by simp
              then have a40:"v' = v" using convertSame[of t2 t' v v'] 1(3) by simp
              moreover have "typeCon t' v" using a40 1 2(1) 2(3)
                by (simp add: typeConConvert)
              moreover have "x1 = v"
                using sameLoc a30 a40 KValue 1(4) notNoneUpdate[of st' g' l2 "(KValue x1)" ] notNoneUpdate[of st' g' l2 "(KValue v')" ] by simp
              ultimately have "typeCon t' x1" by simp
              then show ?thesis using True KValue by auto
            next
              case (KCDptr x2)
              then show ?thesis using a30 "1"(4) by (simp add:sameLoc)
            next
              case (KMemptr x3)
              then show ?thesis using a30 "1"(4) by (simp add:sameLoc)
            next
              case (KStoptr x4)
              then show ?thesis using a30 "1"(4) by (simp add:sameLoc)
            qed
          qed
        qed

      next
        fix x2 assume a20:"l = Storeloc x2"
        then have "(Storage st' (Address env)) = (Storage st (Address env))" using 1(4) by simp
        then show "case t of type.Storage typ \<Rightarrow> SCon typ x2 (Storage st' (Address env)) | _ \<Rightarrow> False"
          using a10 a20 2(1) unfolding TypeSafe_def typeCompat_def by (cases t; force)
      qed
    qed
  next
    show "unique_locations (Denvalue env)" using 2(1) typeSafeUnique by auto
  next
    have "(Accounts st) = Accounts(st')" using 1(4) by simp
    then show "balanceTypes (Accounts st')" using balanceTypes_def balanceTypes_def 2(1) typeSafeAccounts by simp
  next
    show " compPointers (Stack st') (Denvalue env)" unfolding compPointers_def
    proof(intros)
      fix tp1 tp2 l1 l22 l1' l2' stl1 stl2
      assume a1:"(type.Storage tp1, l1) |\<in>| fmran (Denvalue env) \<and>
     (type.Storage tp2, l22) |\<in>| fmran (Denvalue env) \<and>
     (l1 = Stackloc l1' \<and> accessStore l1' (Stack st') = Some (KStoptr stl1) \<or> l1 = Storeloc stl1) \<and>
     (l22 = Stackloc l2' \<and> accessStore l2' (Stack st') = Some (KStoptr stl2) \<or> l22 = Storeloc stl2)"
      then have 10:"accessStore l1' (Stack st) = Some (KStoptr stl1) \<or> l1 = Storeloc stl1" using 1(4) 2(1) updateOneType[of st' g' l2 "(KValue v')" st "(KStoptr stl1)" l1' ] by auto
      then have 20:"accessStore l2' (Stack st) = Some (KStoptr stl2) \<or> l22 = Storeloc stl2" using a1 1(4) 2(1) updateOneType[of st' g' l2 "(KValue v')" st "(KStoptr stl2)" l2' ] by auto
      have "Storage st' (Address env) = (Storage st (Address env))" using a1 1(4) 2(1) updateOneType[of st' g' l2 "(KValue v')" st "(KStoptr stl2)" l2' ] by auto
      then show "if TypedStoSubpref stl2 stl1 tp1 then CompStoType tp1 tp2 stl1 stl2 else if TypedStoSubpref stl1 stl2 tp2 then CompStoType tp2 tp1 stl2 stl1 else True"
        using 2(1) a1 10 20 unfolding TypeSafe_def compPointers_def by blast
    qed
  next
    show "svalueTypes (Svalue env)" using svalueTypes_def typeSafeSvalue 2(1) by simp
  next
    have "(Storage st') = (Storage st)" using 1(4) by simp
    then show "safeContract (Accounts st') (Storage st')" using 2(1) 1(4) unfolding safeContract_def TypeSafe_def
      by fastforce
  next
    have a10:"Toploc (Stack st') = Toploc (Stack st)" using 1(4) unfolding updateStore_def by simp
    then have "(Value t', Stackloc l2) |\<in>| fmran (Denvalue env)" using 2(1) 1(2) lexpStackloc_imps_inDen by simp
    then have a20:"\<exists>val. accessStore l2 (Stack st) = Some val" using typeSafeLocExists 2(1) TypeSafe_def by blast
    then have a30:"(\<forall>tloc loc. Toploc (Stack st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Stack st) = None)
                   \<and>(\<forall>loc y. accessStore loc (Stack st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Stack st). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))"
      using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by simp
    then have a40:"(\<forall>tloc loc. Toploc (Stack st') \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Stack st) = None)
                    \<and>(\<forall>loc y. accessStore loc (Stack st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Stack st'). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))"
      using a10 by simp
    show "lessThanTopLocs (Stack st')" unfolding lessThanTopLocs_def
    proof intros
      fix tloc loc
      assume *:"Toploc (Stack st') \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
      then show "accessStore loc (Stack st') = None"
      proof(cases "loc = l2")
        case True
        then show ?thesis using * a10
          by (metis a20 a30 option.distinct(1))
      next
        case False
        then have a50:"accessStore loc (Stack st) = accessStore loc (Stack st')" using 1(4) unfolding updateStore_def accessStore_def by simp
        then show ?thesis using 2(1) a40 * a10 False a30 by simp
      qed
    next
      fix loc y
      assume *:" accessStore loc (Stack st') = Some y "
      show "\<exists>tloc<Toploc (Stack st'). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
      proof(cases "loc = l2")
        case True
        then show ?thesis using *a10 a20 a30 by simp
      next
        case False
        then have a50:"accessStore loc (Stack st) = accessStore loc (Stack st')" using 1(4) unfolding updateStore_def accessStore_def by simp
        then show ?thesis using * 2(1) a40 by simp
      qed
    qed
  next
    show "lessThanTopLocs cd" using 2(1) unfolding TypeSafe_def using 1 by auto
  next
    show "lessThanTopLocs (Memory st')" using 2(1) unfolding TypeSafe_def using 1 by auto
  next
    have "envAddressesWellFormed env" using 2(1) unfolding TypeSafe_def by auto
    then show "addressFormat (Address env)" and "addressFormat (Sender env)" by simp+
  next
    show "AddressTypes (Accounts st')" using 2(1) unfolding TypeSafe_def using 1 by simp
  next
    have "Accounts st'= Accounts st" using 1 by auto
    then show "fullyInitialised env (Accounts st') (Stack st')" using 2(3) 1(4) unfolding fullyInitialised_def updateStore_def accessStore_def by auto
  next
    have cc0:"\<forall>l ptr_loc. accessStore l (Stack st') = Some (KMemptr ptr_loc) \<longrightarrow> accessStore l (Stack st) = Some (KMemptr ptr_loc)"
      using 1(4) unfolding updateStore_def accessStore_def by auto
    show "denvalueTypeCorrectness env (Stack st') (Memory st')"
      unfolding denvalueTypeCorrectness_def
    proof intros
      fix t l ptr_loc
      assume "(type.Memory t, Stackloc l) |\<in>| fmran (Denvalue env) \<and>
     accessStore l (Stack st') = Some (KMemptr ptr_loc)"
      then have "(case t of
       MTArray len arr \<Rightarrow> (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr)
       | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st) = Some (MTValue val))"
        using 2(1) unfolding TypeSafe_def denvalueTypeCorrectness_def using cc0 by blast
      moreover have "Memory st = Memory st'" using 1(4) by simp
      ultimately show "case t of
     MTArray len arr \<Rightarrow> (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr)
     | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st') = Some (MTValue val)"
        by metis
    qed
  next
    show "subPrefixStructuralConsistency (Memory st')"
      using 2(1) 1(4) unfolding TypeSafe_def by simp
  next
    show "SomeValSomeTyp (Memory st') " using 2(1) unfolding TypeSafe_def using 1(4) by auto
  next
    show "\<And>locs t. accessTypeStore locs (Memory st) = Some t \<Longrightarrow> accessTypeStore locs (Memory st') = Some t"
      using 1 by simp
  next
    show "\<And>locs v. accessStore locs (Memory st) = Some (MPointer v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MPointer v')"
      using 1 by simp
  next
    show "\<And>locs v. accessStore locs (Memory st) = Some (MValue v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MValue v')"
      using 1 by simp
  next
    show " \<And>i loc. i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<Longrightarrow> accessStore loc
        (Memory st) = None \<Longrightarrow> accessStore loc (Memory st') = None"
      using 1 by simp
  next
    show "Toploc (Memory st) \<le> Toploc (Memory st')" using 1 by simp
  qed
qed

text \<open>Assignment case 2: a value assigned to a storage location.\<close>

lemma TypeSafe_Assign_2:
  assumes "TypeSafe env (Accounts st) (Stack st) (Memory st) (Storage st) cd"
    and "stmt (ASSIGN lv ex) env cd st = Normal ((), st')"
    and "fullyInitialised env (Accounts st) (Stack st)"
    and "expr ex env cd (st\<lparr>state.Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>) (state.Gas st - costs (ASSIGN lv ex) env cd st) = Normal ((KValue v, Value t2), g)"
    and "lexp lv env cd (st\<lparr>state.Gas := g\<rparr>) g = Normal((LStoreloc locationChanged, type.Storage (STValue t')),g')"
    and "convert t2 t' v = Some v'"
    and "st' = st\<lparr>state.Gas := g', Storage := (Storage st) (Address env := (fmupd locationChanged v' (Storage st (Address env))))\<rparr>"
  shows "StateInvariant env st st' cd"
proof -
  let ?case = "StateInvariant env st st' cd"
  note 2 = assms(1-3)
  note subcase2 = assms(4-7)
  then have tpCon:"typeCon t2 (extractValueType (KValue v)) \<and> (\<exists>xx. KValue v = KValue xx)"
    using exprTypeconInduct(3)[of ex env cd "(st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)" "(state.Gas st - costs (ASSIGN lv ex) env cd st)" "KValue v" "Value t2" g]
    using 2(1) 2(3) unfolding fullyInitialised_def by force
  then have tcon:"typeCon t' v'" using typeSafeConvert[of t2 "(extractValueType (KValue v))" t' ] subcase2(3)
    by (metis convertSame extractValueType.simps(1))
  have stacksSame:"Stack st = Stack st'" using subcase2(4) by simp
  have accessStoreSt:"Storage st' (Address env) $$ locationChanged = Some v'" using subcase2 by simp
  then have scont':"SCon (STValue t') locationChanged (Storage st' (Address env))"
    using SCon.simps(1)[of t' locationChanged "Storage st' (Address env)"] accessStorage_def tcon by simp
  have nonLocChanged:"\<forall>l. l \<noteq> locationChanged \<longrightarrow> Storage st' (Address env) $$ l = Storage st (Address env) $$ l" using subcase2 by simp
  show ?thesis unfolding TypeSafe_def StateInvariant_def
  proof intros
    show "unique_locations (Denvalue env)" using 2(1) typeSafeUnique by simp
  next
    have "compPointers (Stack st) (Denvalue env)" using 2(1) unfolding TypeSafe_def by simp
    show "compPointers (Stack st') (Denvalue env)" unfolding compPointers_def using 2(1) compPointers_def stacksSame typeSafeCompPointers by force

  next
    show "safeContract (Accounts st') (Storage st')" unfolding safeContract_def
    proof intros
      fix e ct dud i tp
      assume *:"Type (Accounts st' (Address (e::environment))) = Some (atype.Contract (Contract e)) \<and>
               ep $$ Contract (e::environment) = Some (ct, dud) \<and>
               ct $$ i = Some (Var tp)"
      have scOld:"safeContract (Accounts st) (Storage st)" using 2(1) unfolding TypeSafe_def by simp
      show "SCon tp i (Storage st' (Address e))"
      proof (cases "Address e = Address env")
        case False
        have stoEq:"\<forall>a. a \<noteq> Address env \<longrightarrow> Storage st' a = Storage st a"
          using subcase2(4) by simp
        have typedOld:"Type (Accounts st (Address e)) = Some (atype.Contract (Contract e))"
          using * subcase2(4) by simp
        have epOld:"ep $$ Contract e = Some (ct, dud)"
          using * by simp
        have ctOld:"ct $$ i = Some (Var tp)"
          using * by simp
        show ?thesis
          using safeContract_other_address_preserved[OF scOld stoEq False typedOld epOld ctOld] .
      next
        case addrEq:True
        obtain c where **:"Type (Accounts st (Address env)) = Some (atype.Contract c) \<and> Contract env = c"
          using 2(3) unfolding fullyInitialised_def using 2 by blast
        have cEq:"Contract e = Contract env"
          using * ** addrEq subcase2(4) by auto
        have typedOld:"Type (Accounts st (Address e)) = Some (atype.Contract (Contract e))"
          using * subcase2(4) by simp
        have epOld:"ep $$ Contract e = Some (ct, dud)"
          using * by simp
        have ctOld:"ct $$ i = Some (Var tp)"
          using * by simp
        have denI:"Denvalue env $$ i = Some (type.Storage tp, Storeloc i)"
          using fi_contract_var_to_denvalue_storeloc[OF 2(3) addrEq typedOld epOld ctOld] .
        have inDenI:"(type.Storage tp, Storeloc i) |\<in>| fmran (Denvalue env)"
          using denI by (simp add: fmranI)
        have oldSCon:"SCon tp i (Storage st (Address env))"
          using safeContract_field_scon_from_typeCompat[OF 2(1) 2(3) addrEq typedOld epOld ctOld] .
        have uniq:"unique_locations (Denvalue env)"
          using 2(1) typeSafeUnique by simp
        have epEnv:"ep $$ Contract env = Some (ct, dud)"
          using epOld cEq by simp
        show ?thesis
        proof(cases rule:lexpStorage[OF 2(1) subcase2(2) 2(3)])
          case 1
          then have inDenChanged:"(type.Storage (STValue t'), Storeloc locationChanged) |\<in>| fmran (Denvalue env)" by simp
          show ?thesis
          proof(cases "i = locationChanged")
            case True
            have pairEq:"(type.Storage tp, Storeloc i) = (type.Storage (STValue t'), Storeloc locationChanged)"
              using uniqueLocs[OF uniq inDenI inDenChanged] True by simp
            then have tpEq:"tp = STValue t'" by simp
            show ?thesis using scont' True tpEq by (simp add: addrEq)
          next
            case False
            have ctChanged:"ct $$ locationChanged = Some (Var (STValue t'))"
              using fi_denvalue_storeloc_to_contract_var[OF 2(3) epEnv inDenChanged] .
            have n1:"\<not>TypedStoSubpref locationChanged i tp"
                and n2:"\<not>TypedStoSubpref i locationChanged (STValue t')"
              using methodVarsNoPref False epOld ctOld ctChanged by blast+
            have relChanged:"TypedStoSubpref locationChanged locationChanged (STValue t')
                             \<and> CompStoType (STValue t') (STValue t') locationChanged locationChanged"
              by simp
            show ?thesis
              using singleLocChanged_nonchanged_SCon[OF nonLocChanged False oldSCon n1 n2 relChanged]
              by (simp add: addrEq)
          qed
        next
          case sub2:(2 l t)
          have inDenL:"(type.Storage t, Storeloc l) |\<in>| fmran (Denvalue env)" using sub2 by simp
          have relL:"TypedStoSubpref locationChanged l t \<and> CompStoType t (STValue t') l locationChanged" using sub2 by simp
          show ?thesis
          proof(cases "i = l")
            case True
            have pairEq:"(type.Storage tp, Storeloc i) = (type.Storage t, Storeloc l)"
              using uniqueLocs[OF uniq inDenI inDenL] True by simp
            then have tpEq:"tp = t" by simp
            have comp:"CompStoType tp (STValue t') i locationChanged"
              using relL tpEq True by simp
            show ?thesis using SCon_value_write_imps_SCon[OF comp oldSCon scont' nonLocChanged]
              by (simp add: addrEq)
          next
            case False
            have ctL:"ct $$ l = Some (Var t)"
              using fi_denvalue_storeloc_to_contract_var[OF 2(3) epEnv inDenL] by simp
            have n1:"\<not>TypedStoSubpref l i tp"
                and n2:"\<not>TypedStoSubpref i l t"
              using methodVarsNoPref False epOld ctOld ctL by blast+
            have iNeChanged:"i \<noteq> locationChanged"
            proof
              assume "i = locationChanged"
              then have "TypedStoSubpref i l t" using relL by simp
              then show False using n2 by contradiction
            qed
            show ?thesis
              using singleLocChanged_nonchanged_SCon[OF nonLocChanged iNeChanged oldSCon n1 n2 relL]
              by (simp add: addrEq)
          qed
        next
          case (3 l' t l)
          have inDenStk:"(type.Storage t, Stackloc l) |\<in>| fmran (Denvalue env)" using 3 by simp
          have ptrL:"accessStore l (Stack st) = Some (KStoptr l')" using 3 by simp
          have rel0:"TypedStoSubpref locationChanged l' t \<and> CompStoType t (STValue t') l' locationChanged" using 3 by simp
          obtain tprnt lprnt where
              inDenPr:"(type.Storage tprnt, Storeloc lprnt) |\<in>| fmran (Denvalue env)"
              and compPr:"CompStoType tprnt t lprnt l'"
            using fiPtr_parent_from_fullyInitialised[OF 2(3) inDenStk ptrL] by blast
          have compPr2:"CompStoType tprnt (STValue t') lprnt locationChanged"
            using compPr rel0 CompStoType_trns by blast
          have relPr:"TypedStoSubpref locationChanged lprnt tprnt \<and> CompStoType tprnt (STValue t') lprnt locationChanged"
            using compPr2 CompStoType_imps_TypedStoSubpref by blast
          show ?thesis
          proof(cases "i = lprnt")
            case True
            have pairEq:"(type.Storage tp, Storeloc i) = (type.Storage tprnt, Storeloc lprnt)"
              using uniqueLocs[OF uniq inDenI inDenPr] True by simp
            then have tpEq:"tp = tprnt" by simp
            have comp:"CompStoType tp (STValue t') i locationChanged"
              using compPr2 tpEq True by simp
            show ?thesis using SCon_value_write_imps_SCon[OF comp oldSCon scont' nonLocChanged]
              by (simp add: addrEq)
          next
            case False
            have ctPr:"ct $$ lprnt = Some (Var tprnt)"
              using fi_denvalue_storeloc_to_contract_var[OF 2(3) epEnv inDenPr] .
            have n1:"\<not>TypedStoSubpref lprnt i tp"
                and n2:"\<not>TypedStoSubpref i lprnt tprnt"
              using methodVarsNoPref False epOld ctOld ctPr by blast+
            have iNeChanged:"i \<noteq> locationChanged"
            proof
              assume "i = locationChanged"
              then have "TypedStoSubpref i lprnt tprnt" using relPr by simp
              then show False using n2 by contradiction
            qed
            show ?thesis
              using singleLocChanged_nonchanged_SCon[OF nonLocChanged iNeChanged oldSCon n1 n2 relPr]
              by (simp add: addrEq)
          qed
        qed
      qed
    qed
  next
    have "Accounts st' = Accounts st" using subcase2(4) by simp
    then show "balanceTypes (Accounts st')" using 2(1) unfolding TypeSafe_def balanceTypes_def by simp
  next
    show "svalueTypes (Svalue env)" using 2(1) unfolding TypeSafe_def by simp
  next
    have "Stack st = Stack st'" using subcase2(4) by simp
    then show "lessThanTopLocs (Stack st')" using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by simp
  next
    show "typeCompat (Denvalue env) (Stack st') (Memory st') (Storage st' (Address env)) cd" unfolding typeCompat_def
    proof intros
      fix t l
      assume inDen:"(t, l) |\<in>| fmran (Denvalue env)"
      then show "denvalueCon (Stack st') (Memory st') (Storage st' (Address env)) cd t l"
      proof (cases l)
        case (Stackloc loc)
        then have "l \<noteq> Storeloc locationChanged" by simp
        then have same:"accessStore loc (Stack st) = accessStore loc (Stack st')" using subcase2(4) by simp
        then show ?thesis
        proof(cases "accessStore loc (Stack st')")
          case None
          then show ?thesis using same 2(1) inDen Stackloc unfolding TypeSafe_def typeCompat_def by fastforce
        next
          case (Some a)
          have samemem:"(Memory st) = Memory st'" using subcase2(4) by simp
          then show ?thesis
          proof(cases a)
            case (KValue x1)
            then show ?thesis using Some same 2(1) inDen Stackloc unfolding TypeSafe_def typeCompat_def by fastforce
          next
            case (KCDptr x2)
            then show ?thesis using Some same 2(1) inDen Stackloc unfolding TypeSafe_def typeCompat_def samemem by fastforce
          next
            case (KMemptr x3)
            then show ?thesis using Some same 2(1) inDen Stackloc unfolding TypeSafe_def typeCompat_def samemem by fastforce
          next
            case (KStoptr x4)
            then have a20:"accessStore loc (Stack st) = Some (KStoptr x4)" using same Some by simp
            have a25:"denvalueCon (Stack st) (Memory st) (Storage st (Address env)) cd t l"
              using 2(1) unfolding TypeSafe_def typeCompat_def using inDen by simp
            then obtain struct where a30:"t = type.Storage struct" using a20 Stackloc by (simp split:type.splits)
            then have a40:"SCon struct x4 (Storage st (Address env))" using a25 a20 Stackloc by (simp split:type.splits)
            have tCont2v:"typeCon t2 v" using subcase2(1) extractValueType.simps 2(1)
              using exprTypeconInduct(3)[of ex env cd "(st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)"
                  "(state.Gas st - costs (ASSIGN lv ex) env cd st)" "KValue v" "Value t2" g]
              using 2(3) unfolding fullyInitialised_def
              by (simp)
            have "v' = v" using convertSame[of t2 t' v v'] subcase2(3) by simp
            then have tCont'v:"typeCon t' v" using typeSafeConvert[of t2 v t'] subcase2(3) tCont2v by simp
            have "SCon struct x4 (Storage st' (Address env))" using a40 a30 inDen
            proof(cases "TypedStoSubpref locationChanged x4 struct")
              case subloc:True
              have compPtr:"(\<forall>tp1 tp2 l1 l2 l1' l2' stl1 stl2.
                      (type.Storage tp1, l1) |\<in>| fmran (Denvalue env) \<and>
                      (type.Storage tp2, l2) |\<in>| fmran (Denvalue env) \<and>
                      (l1 = Stackloc l1' \<and> accessStore l1' (Stack st) = Some (KStoptr stl1) \<or> l1 = Storeloc stl1)
                      \<and> (l2 = Stackloc l2' \<and> accessStore l2' (Stack st) = Some (KStoptr stl2) \<or> l2 = Storeloc stl2) \<longrightarrow>
                      (if TypedStoSubpref stl2 stl1 tp1 then CompStoType tp1 tp2 stl1 stl2 else if TypedStoSubpref stl1 stl2 tp2 then CompStoType tp2 tp1 stl2 stl1 else True))"
                using 2(1) unfolding TypeSafe_def compPointers_def by auto
              then show ?thesis
              proof(cases rule:lexpStorage[OF 2(1) subcase2(2) 2(3)])
                case 11:1
                then have b40:"CompStoType struct (STValue t') x4 locationChanged"
                  using inDen Stackloc Some KStoptr a20 a30 compPtr subloc by metis
                then show ?thesis
                  using SCon_value_write_imps_SCon[OF _ a40 scont' nonLocChanged] by blast
              next
                case (2 l'' t'')
                have c3:"\<forall>l struct. \<not>TypedStoSubpref locationChanged l struct \<longrightarrow> Storage st' (Address env) $$ l = Storage st (Address env) $$ l"
                  by (metis TypedStoSubpref_sameLoc nonLocChanged)
                have b40:"if TypedStoSubpref x4 l'' t'' then CompStoType t'' struct l'' x4
                                else if TypedStoSubpref l'' x4 struct then CompStoType struct t'' x4 l''
                                  else True"
                  using compPtr inDen Stackloc Some KStoptr a20 a30 2 by blast
                then show ?thesis using subloc 2
                proof(cases "x4 = l''")
                  case True
                  then have stt:"struct = t''" using b40
                    using CompStoType_sameLoc_sameType TypedStoSubpref_sameLoc by auto
                  then show ?thesis
                  proof(cases "l'' = locationChanged")
                    case t4:True
                    then show ?thesis using stt True scont'
                      using "2"(2) CompStoType_sameLoc_sameType by blast
                  next
                    case False
                    have c0:"CompStoType struct (STValue t') x4 locationChanged" using 2(2) True stt by simp
                    then have "\<exists>y. hash l'' y = locationChanged" using subloc "2"(2) TypedStoSubpref_b False by auto
                    then obtain i'' where c1:"(hash x4 i'' = locationChanged)" using CompStoType_imps_subloc False True by blast
                    then show ?thesis using stvalueLocationsInduct a40 scont' c0 nonLocChanged c3 by blast
                  qed
                next
                  case x4Dif:False
                  then show ?thesis
                  proof(cases "TypedStoSubpref x4 l'' t''")
                    case d5:True
                    then have d7:"CompStoType t'' struct l'' x4" using b40 by simp
                    have d9:"CompStoType t'' (STValue t') l'' locationChanged" using 2(2) by simp
                    have d10:"CompStoType struct (STValue t') x4 locationChanged" using CompStoType_subloc_type_transfer[of t'' t' l'' locationChanged struct x4] subloc d7 d9 by blast
                    then have d11:"\<exists>x. hash l'' x = x4" using TypedStoSubpref_b x4Dif d5 by auto
                    then show ?thesis
                    proof(cases "l'' = locationChanged")
                      case True
                      then obtain i'' where d11:"hash locationChanged i'' = x4" using d11 by auto
                      then show ?thesis using subloc using TypedStoSubpref_hashes by auto
                    next
                      case False
                      then have "\<exists>x. hash l'' x = locationChanged" using 2(2) TypedStoSubpref_b by auto
                      then have "\<exists>x. hash l'' x = x4" using d11 using hash_suffixes_associative by auto
                      then show ?thesis
                      proof(cases "x4 = locationChanged")
                        case True
                        then have "struct = (STValue t')" using d10 by (simp add: CompStoType_sameLoc_sameType)
                        then show ?thesis using True scont' by auto
                      next
                        case False
                        then obtain i'' where d11:"hash x4 i'' = locationChanged"
                          using subloc False TypedStoSubpref_b[of locationChanged x4 struct] by blast
                        then show ?thesis using stvalueLocationsInduct a40 scont' nonLocChanged c3 d11 d10 by blast
                      qed
                    qed
                  next
                    case f5:False
                    then show ?thesis
                    proof(cases "TypedStoSubpref l'' x4 struct")
                      case True
                      then have d5:"TypedStoSubpref l'' x4 struct" by simp
                      then have d7:"CompStoType struct t'' x4 l''" using b40 f5 by simp
                      then have d10:"\<exists>x. hash x4 x = l''" using TypedStoSubpref_b x4Dif d5 by auto
                      then show ?thesis
                      proof(cases "l'' = locationChanged")
                        case True
                        then obtain i'' where d11:"hash x4 i'' = locationChanged" using d10 by auto
                        then have d15:"t'' = STValue t'" using 2(2) CompStoType_sameLoc_sameType True by auto
                        then have c0:"CompStoType struct (STValue t') x4 locationChanged" using 2(2) d15 d7 by fastforce
                        then show ?thesis using stvalueLocationsInduct a40 scont' c0 nonLocChanged c3 d11 by blast
                      next
                        case False
                        then have "\<exists>x. hash l'' x = locationChanged" using 2(2) TypedStoSubpref_b by auto
                        then have "\<exists>x. hash x4 x = locationChanged" using d10 using hash_suffixes_associative by auto
                        then obtain i'' where d11:"hash x4 i'' = locationChanged" by auto
                        then have "CompStoType struct (STValue t') x4 locationChanged" using CompStoType_trns 2(2) d7 by blast
                        then show ?thesis using stvalueLocationsInduct a40 scont' nonLocChanged c3 d11 by blast
                      qed
                    next
                      case False
                      have "x4 \<noteq> locationChanged" using 2(2) f5 by blast
                      then show ?thesis using a40 False f5 2(2) singleLocChanged_nonchanged_SCon
                        using nonLocChanged by blast
                    qed
                  qed
                qed
              next
                case (3 l'' t'' l)
                have c3:"\<forall>l struct. \<not>TypedStoSubpref locationChanged l struct \<longrightarrow> Storage st' (Address env) $$ l = Storage st (Address env) $$ l"
                  by (metis TypedStoSubpref_sameLoc nonLocChanged)
                then have b40:"if TypedStoSubpref x4 l'' t'' then CompStoType t'' struct l'' x4
                                else if TypedStoSubpref l'' x4 struct then CompStoType struct t'' x4 l''
                                  else True"
                  using compPtr inDen Stackloc Some KStoptr a20 a30 3 by blast
                then show ?thesis using subloc 2
                proof(cases "x4 = l''")
                  case True
                  then have stt:"struct = t''" using b40
                    using CompStoType_sameLoc_sameType TypedStoSubpref_sameLoc by auto
                  then show ?thesis
                  proof(cases "l'' = locationChanged")
                    case t4:True
                    then show ?thesis using stt True scont'
                      using "3"(3) CompStoType_sameLoc_sameType by blast
                  next
                    case False
                    have c0:"CompStoType struct (STValue t') x4 locationChanged" using 3(3) True stt by simp
                    then have "\<exists>y. hash l'' y = locationChanged" using subloc 3(3) TypedStoSubpref_b False by auto
                    then obtain i'' where c1:"(hash x4 i'' = locationChanged)" using CompStoType_imps_subloc False True by blast
                    then show ?thesis using stvalueLocationsInduct a40 scont' c0 nonLocChanged c3 by blast
                  qed
                next
                  case x4Dif:False
                  then show ?thesis
                  proof(cases "TypedStoSubpref x4 l'' t''")
                    case d5:True
                    then have d7:"CompStoType t'' struct l'' x4" using b40 by simp
                    have d9:"CompStoType t'' (STValue t') l'' locationChanged" using 3(3) by simp
                    have d10:"CompStoType struct (STValue t') x4 locationChanged" using CompStoType_subloc_type_transfer[of t'' t' l'' locationChanged struct x4] subloc d7 d9 by blast
                    then have d11:"\<exists>x. hash l'' x = x4" using TypedStoSubpref_b x4Dif d5 by auto
                    then show ?thesis
                    proof(cases "l'' = locationChanged")
                      case True
                      then obtain i'' where d11:"hash locationChanged i'' = x4" using d11 by auto
                      then show ?thesis using subloc using TypedStoSubpref_hashes by auto
                    next
                      case False
                      then have "\<exists>x. hash l'' x = locationChanged" using 3(3) TypedStoSubpref_b by auto
                      then have "\<exists>x. hash l'' x = x4" using d11 using hash_suffixes_associative by auto
                      then show ?thesis
                      proof(cases "x4 = locationChanged")
                        case True
                        then have "struct = (STValue t')" using d10 by (simp add: CompStoType_sameLoc_sameType)
                        then show ?thesis using True scont' by auto
                      next
                        case False
                        then obtain i'' where d11:"hash x4 i'' = locationChanged"
                          using subloc False TypedStoSubpref_b[of locationChanged x4 struct] by blast
                        then show ?thesis using stvalueLocationsInduct a40 scont' nonLocChanged c3 d11 d10 by blast
                      qed
                    qed
                  next
                    case f5:False
                    then show ?thesis
                    proof(cases "TypedStoSubpref l'' x4 struct")
                      case True
                      then have d5:"TypedStoSubpref l'' x4 struct" by simp
                      then have d7:"CompStoType struct t'' x4 l''" using b40 f5 by simp
                      then have d10:"\<exists>x. hash x4 x = l''" using TypedStoSubpref_b x4Dif d5 by auto
                      then show ?thesis
                      proof(cases "l'' = locationChanged")
                        case True
                        then obtain i'' where d11:"hash x4 i'' = locationChanged" using d10 by auto
                        then have d15:"t'' = STValue t'" using 3(3) CompStoType_sameLoc_sameType True by auto
                        then have c0:"CompStoType struct (STValue t') x4 locationChanged" using 3(3) d15 d7 by fastforce
                        then show ?thesis using stvalueLocationsInduct a40 scont' c0 nonLocChanged c3 d11 by blast
                      next
                        case False
                        then have "\<exists>x. hash l'' x = locationChanged" using 3(3) TypedStoSubpref_b by auto
                        then have "\<exists>x. hash x4 x = locationChanged" using d10 using hash_suffixes_associative by auto
                        then obtain i'' where d11:"hash x4 i'' = locationChanged" by auto
                        then have "CompStoType struct (STValue t') x4 locationChanged" using CompStoType_trns 3(3) d7 by blast
                        then show ?thesis using stvalueLocationsInduct a40 scont' nonLocChanged c3 d11 by blast
                      qed
                    next
                      case False
                      have "x4 \<noteq> locationChanged" using f5
                        using "3"(3) by auto
                      then show ?thesis using a40 False f5 3(3) singleLocChanged_nonchanged_SCon
                        using nonLocChanged by blast
                    qed
                  qed
                qed
              qed
            next
              case f1:False
              then show ?thesis using a40
              proof(induction struct arbitrary:x4)
                case (STArray x1 struct)
                have b10:"\<forall>i<x1. SCon struct (hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Storage st (Address env))"
                  using STArray(3) using SCon.simps(2)[of x1 struct x4 "(Storage st (Address env))"] by auto
                have b20:"\<forall>i<x1. \<not> TypedStoSubpref locationChanged (hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) struct
                                  \<and> locationChanged \<noteq> hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i)"
                  using STArray(2) TypedStoSubpref.simps(2)[of locationChanged x4 x1 struct]
                  using TypedStoSubpref_sameLoc by auto
                then have b30:"\<forall>i<x1. \<not> TypedStoSubpref locationChanged (hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) struct " by auto
                have " (\<forall>i<x1. SCon struct (hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Storage st' (Address env)))"
                proof(intros)
                  fix i assume b40: "i<x1"
                  then have "\<not>TypedStoSubpref locationChanged (hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) struct" using b30 by auto
                  then show "SCon struct (hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Storage st' (Address env))" using STArray(1)[of
                      "(hash x4 (ShowL\<^sub>n\<^sub>a\<^sub>t i))"] b30 b10 b40 by simp
                qed
                then show ?case using SCon.simps(2)[of x1 struct x4 "Storage st' (Address env)"] by simp
              next
                case (STMap x1 struct)
                then have " (\<forall>i. typeCon x1 i \<longrightarrow> SCon struct (hash x4 i) (Storage st (Address env)))" using SCon.simps(3)[of x1 struct x4 "(Storage st (Address env))"] by simp
                moreover have "(\<forall>i. \<not>typeCon x1 i \<or> \<not>TypedStoSubpref locationChanged (hash x4 i) struct \<and> locationChanged \<noteq> hash x4 i)"
                  using STMap(2) TypedStoSubpref.simps(3)[of locationChanged x4 x1 struct]
                  using TypedStoSubpref_sameLoc by auto
                ultimately show ?case using STMap(1) by auto
              next
                case (STValue x)
                then have c5:"(x4 \<noteq> locationChanged \<or> STValue t' \<noteq> STValue x)" using Subpref.simps(1)[of x x4 "STValue t'" locationChanged] by auto
                then show ?case
                proof(cases "x4 \<noteq> locationChanged")
                  case True
                  then have c10:"Storage st' (Address env) $$ x4 = Storage st (Address env) $$ x4" using subcase2 nonLocChanged by auto
                  then have " SCon (STValue x) x4 (Storage st (Address env))" using STValue by blast
                  then show ?thesis using c10
                    by (simp add: accessStorage_def)
                next
                  case False
                  then have "x4 = locationChanged" by simp
                  then have "STValue t' = STValue x" using subcase2 Stackloc KStoptr inDen lexpStorage[of env st cd lv g locationChanged t' g'] Some f1 2(1) a20 a30
                    by (metis STValue.prems(1) TypedStoSubpref.simps(1))
                  then show ?thesis using False c5 by auto
                qed
              qed
            qed
            then show ?thesis using Stackloc inDen KStoptr Some a30 subcase2 by simp
          qed
        qed
      next
        case (Storeloc x2)
        then have a20:"case t of type.Storage typ \<Rightarrow> SCon typ x2 (Storage st (Address env)) | _ \<Rightarrow> False"
          using 2(1) unfolding TypeSafe_def typeCompat_def using inDen by force
        then obtain struct where a30:"t = type.Storage struct" using a20 Storeloc by (simp split:type.splits)
        then have a40:"SCon struct x2 (Storage st (Address env))" using a20 Storeloc by (simp split:type.splits)
        have tCont2v:"typeCon t2 v" using subcase2(1) extractValueType.simps 2(1)
          using exprTypeconInduct(3)[of ex env cd "(st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)" "(state.Gas
              st - costs (ASSIGN lv ex) env cd st)" "KValue v" "Value t2" g]
          using 2(3) unfolding fullyInitialised_def by (simp)
        have "v' = v" using convertSame[of t2 t' v v'] subcase2(3) by simp
        then have tCont'v:"typeCon t' v" using typeSafeConvert[of t2 v t'] subcase2(3) tCont2v by simp
        have "SCon struct x2 (Storage st' (Address env))" using a40 a30 inDen
        proof(cases "TypedStoSubpref locationChanged x2 struct")
          case subloc:True
          have compPtr:"(\<forall>tp1 tp2 l1 l2 l1' l2' stl1 stl2.
                      (type.Storage tp1, l1) |\<in>| fmran (Denvalue env) \<and>
                      (type.Storage tp2, l2) |\<in>| fmran (Denvalue env) \<and>
                      (l1 = Stackloc l1' \<and> accessStore l1' (Stack st) = Some (KStoptr stl1) \<or> l1 = Storeloc stl1)
                      \<and> (l2 = Stackloc l2' \<and> accessStore l2' (Stack st) = Some (KStoptr stl2) \<or> l2 = Storeloc stl2) \<longrightarrow>
                      (if TypedStoSubpref stl2 stl1 tp1 then CompStoType tp1 tp2 stl1 stl2 else if TypedStoSubpref stl1 stl2 tp2 then CompStoType tp2 tp1 stl2 stl1 else True))"
            using 2(1) unfolding TypeSafe_def compPointers_def by auto
          then show ?thesis
          proof(cases rule:lexpStorage[OF 2(1) subcase2(2) 2(3)])
            case 1
            then have b40:"CompStoType struct (STValue t') x2 locationChanged"
              using inDen Storeloc a20 a30 1 compPtr subloc by metis
            then show ?thesis
              using SCon_value_write_imps_SCon[OF _ a40 scont' nonLocChanged] by blast
          next
            case (2 l'' t'')
            have c3:"\<forall>l struct. \<not>TypedStoSubpref locationChanged l struct \<longrightarrow> Storage st' (Address env) $$ l = Storage st (Address env) $$ l"
              by (metis TypedStoSubpref_sameLoc nonLocChanged)
            then have b40:"if TypedStoSubpref x2 l'' t'' then CompStoType t'' struct l'' x2
                                else if TypedStoSubpref l'' x2 struct then CompStoType struct t'' x2 l''
                                  else True"
              using compPtr inDen Storeloc a20 a30 2 by blast
            then show ?thesis using subloc 2
            proof(cases "x2 = l''")
              case True
              then have stt:"struct = t''" using b40
                using CompStoType_sameLoc_sameType TypedStoSubpref_sameLoc by auto
              then show ?thesis
              proof(cases "l'' = locationChanged")
                case t4:True
                then show ?thesis using stt True scont'
                  using "2"(2) CompStoType_sameLoc_sameType by blast
              next
                case False
                have c0:"CompStoType struct (STValue t') x2 locationChanged" using 2(2) True stt by simp
                then have "\<exists>y. hash l'' y = locationChanged" using subloc "2"(2) TypedStoSubpref_b False by auto
                then obtain i'' where c1:"(hash x2 i'' = locationChanged)" using CompStoType_imps_subloc False True by blast
                then show ?thesis using stvalueLocationsInduct a40 scont' c0 nonLocChanged c3 by blast
              qed
            next
              case x4Dif:False
              then show ?thesis
              proof(cases "TypedStoSubpref x2 l'' t''")
                case d5:True
                then have d7:"CompStoType t'' struct l'' x2" using b40 by simp
                have d9:"CompStoType t'' (STValue t') l'' locationChanged" using 2(2) by simp
                have d10:"CompStoType struct (STValue t') x2 locationChanged" using CompStoType_subloc_type_transfer[of t'' t' l'' locationChanged struct x2] subloc d7 d9 by blast
                then have d11:"\<exists>x. hash l'' x = x2" using TypedStoSubpref_b x4Dif d5 by auto
                then show ?thesis
                proof(cases "l'' = locationChanged")
                  case True
                  then obtain i'' where d11:"hash locationChanged i'' = x2" using d11 by auto
                  then show ?thesis using subloc using TypedStoSubpref_hashes by auto
                next
                  case False
                  then have "\<exists>x. hash l'' x = locationChanged" using 2(2) TypedStoSubpref_b by auto
                  then have "\<exists>x. hash l'' x = x2" using d11 using hash_suffixes_associative by auto
                  then show ?thesis
                  proof(cases "x2 = locationChanged")
                    case True
                    then have "struct = (STValue t')" using d10 by (simp add: CompStoType_sameLoc_sameType)
                    then show ?thesis using True scont' by auto
                  next
                    case False
                    then obtain i'' where d11:"hash x2 i'' = locationChanged"
                      using subloc False TypedStoSubpref_b[of locationChanged x2 struct] by blast
                    then show ?thesis using stvalueLocationsInduct a40 scont' nonLocChanged c3 d11 d10 by blast
                  qed
                qed
              next
                case f5:False
                then show ?thesis
                proof(cases "TypedStoSubpref l'' x2 struct")
                  case True
                  then have d5:"TypedStoSubpref l'' x2 struct" by simp
                  then have d7:"CompStoType struct t'' x2 l''" using b40 f5 by simp
                  then have d10:"\<exists>x. hash x2 x = l''" using TypedStoSubpref_b x4Dif d5 by auto
                  then show ?thesis
                  proof(cases "l'' = locationChanged")
                    case True
                    then obtain i'' where d11:"hash x2 i'' = locationChanged" using d10 by auto
                    then have d15:"t'' = STValue t'" using 2(2) CompStoType_sameLoc_sameType True by auto
                    then have c0:"CompStoType struct (STValue t') x2 locationChanged" using 2(2) d15 d7 by fastforce
                    then show ?thesis using stvalueLocationsInduct a40 scont' c0 nonLocChanged c3 d11 by blast
                  next
                    case False
                    then have "\<exists>x. hash l'' x = locationChanged" using 2(2) TypedStoSubpref_b by auto
                    then have "\<exists>x. hash x2 x = locationChanged" using d10 using hash_suffixes_associative by auto
                    then obtain i'' where d11:"hash x2 i'' = locationChanged" by auto
                    then have "CompStoType struct (STValue t') x2 locationChanged" using CompStoType_trns 2(2) d7 by blast
                    then show ?thesis using stvalueLocationsInduct a40 scont' nonLocChanged c3 d11 by blast
                  qed
                next
                  case False
                  have "x2 \<noteq> locationChanged" using 2(2) f5 by blast
                  then show ?thesis using a40 False f5 2(2) singleLocChanged_nonchanged_SCon
                    using nonLocChanged by blast
                qed

              qed
            qed
          next
            case (3 l'' t'' l)
            have c3:"\<forall>l struct. \<not>TypedStoSubpref locationChanged l struct \<longrightarrow> Storage st' (Address env) $$ l = Storage st (Address env) $$ l"
              by (metis TypedStoSubpref_sameLoc nonLocChanged)
            then have b40:"if TypedStoSubpref x2 l'' t'' then CompStoType t'' struct l'' x2
                                else if TypedStoSubpref l'' x2 struct then CompStoType struct t'' x2 l''
                                  else True"
              using compPtr inDen Storeloc a20 a30 3 by blast
            then show ?thesis using subloc 2
            proof(cases "x2 = l''")
              case True
              then have stt:"struct = t''" using b40
                using CompStoType_sameLoc_sameType TypedStoSubpref_sameLoc by auto
              then show ?thesis
              proof(cases "l'' = locationChanged")
                case t4:True
                then show ?thesis using stt True scont'
                  using "3"(3) CompStoType_sameLoc_sameType by blast
              next
                case False
                have c0:"CompStoType struct (STValue t') x2 locationChanged" using 3(3) True stt by simp
                then have "\<exists>y. hash l'' y = locationChanged" using subloc 3(3) TypedStoSubpref_b False by auto
                then obtain i'' where c1:"(hash x2 i'' = locationChanged)" using CompStoType_imps_subloc False True by blast
                then show ?thesis using stvalueLocationsInduct a40 scont' c0 nonLocChanged c3 by blast
              qed
            next
              case x4Dif:False
              then show ?thesis
              proof(cases "TypedStoSubpref x2 l'' t''")
                case d5:True
                then have d7:"CompStoType t'' struct l'' x2" using b40 by simp
                have d9:"CompStoType t'' (STValue t') l'' locationChanged" using 3(3) by simp
                have d10:"CompStoType struct (STValue t') x2 locationChanged" using CompStoType_subloc_type_transfer[of t'' t' l'' locationChanged struct x2] subloc d7 d9 by blast
                then have d11:"\<exists>x. hash l'' x = x2" using TypedStoSubpref_b x4Dif d5 by auto
                then show ?thesis
                proof(cases "l'' = locationChanged")
                  case True
                  then obtain i'' where d11:"hash locationChanged i'' = x2" using d11 by auto
                  then show ?thesis using subloc using TypedStoSubpref_hashes by auto
                next
                  case False
                  then have "\<exists>x. hash l'' x = locationChanged" using 3(3) TypedStoSubpref_b by auto
                  then have "\<exists>x. hash l'' x = x2" using d11 using hash_suffixes_associative by auto
                  then show ?thesis
                  proof(cases "x2 = locationChanged")
                    case True
                    then have "struct = (STValue t')" using d10 by (simp add: CompStoType_sameLoc_sameType)
                    then show ?thesis using True scont' by auto
                  next
                    case False
                    then obtain i'' where d11:"hash x2 i'' = locationChanged"
                      using subloc False TypedStoSubpref_b[of locationChanged x2 struct] by blast
                    then show ?thesis using stvalueLocationsInduct a40 scont' nonLocChanged c3 d11 d10 by blast
                  qed
                qed
              next
                case f5:False
                then show ?thesis
                proof(cases "TypedStoSubpref l'' x2 struct")
                  case True
                  then have d5:"TypedStoSubpref l'' x2 struct" by simp
                  then have d7:"CompStoType struct t'' x2 l''" using b40 f5 by simp
                  then have d10:"\<exists>x. hash x2 x = l''" using TypedStoSubpref_b x4Dif d5 by auto
                  then show ?thesis
                  proof(cases "l'' = locationChanged")
                    case True
                    then obtain i'' where d11:"hash x2 i'' = locationChanged" using d10 by auto
                    then have d15:"t'' = STValue t'" using 3(3) CompStoType_sameLoc_sameType True by auto
                    then have c0:"CompStoType struct (STValue t') x2 locationChanged" using 3(3) d15 d7 by fastforce
                    then show ?thesis using stvalueLocationsInduct a40 scont' c0 nonLocChanged c3 d11 by blast
                  next
                    case False
                    then have "\<exists>x. hash l'' x = locationChanged" using 3(3) TypedStoSubpref_b by auto
                    then have "\<exists>x. hash x2 x = locationChanged" using d10 using hash_suffixes_associative by auto
                    then obtain i'' where d11:"hash x2 i'' = locationChanged" by auto
                    then have "CompStoType struct (STValue t') x2 locationChanged" using CompStoType_trns 3(3) d7 by blast
                    then show ?thesis using stvalueLocationsInduct a40 scont' nonLocChanged c3 d11 by blast
                  qed
                next
                  case False
                  have "x2 \<noteq> locationChanged" using 3(3) f5 by blast
                  then show ?thesis using a40 False f5 3(3) singleLocChanged_nonchanged_SCon
                    using nonLocChanged by blast
                qed
              qed
            qed
          qed
        next
          case f1:False
          then show ?thesis using a40
          proof(induction struct arbitrary:x2)
            case (STArray x1 struct)
            have b10:"\<forall>i<x1. SCon struct (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Storage st (Address env))"
              using STArray(3) using SCon.simps(2)[of x1 struct x2 "(Storage st (Address env))"] by auto
            have b20:"\<forall>i<x1. \<not> TypedStoSubpref locationChanged (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) struct
                                  \<and> locationChanged \<noteq> hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)"
              using STArray(2) TypedStoSubpref.simps(2)[of locationChanged x2 x1 struct]
              using TypedStoSubpref_sameLoc by auto
            then have b30:"\<forall>i<x1. \<not> TypedStoSubpref locationChanged (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) struct " by auto
            have " (\<forall>i<x1. SCon struct (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Storage st' (Address env)))"
            proof(intros)
              fix i assume b40: "i<x1"
              then have "\<not>TypedStoSubpref locationChanged (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) struct" using b30 by auto
              then show "SCon struct (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Storage st' (Address env))" using STArray(1)[of "(hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i))"] b30 b10 b40 by simp
            qed
            then show ?case using SCon.simps(2)[of x1 struct x2 "Storage st' (Address env)"] by simp
          next
            case (STMap x1 struct)
            then have " (\<forall>i. typeCon x1 i \<longrightarrow> SCon struct (hash x2 i) (Storage st (Address env)))" using SCon.simps(3)[of x1 struct x2 "(Storage st (Address env))"] by simp
            moreover have "(\<forall>i. \<not>typeCon x1 i \<or> \<not>TypedStoSubpref locationChanged (hash x2 i) struct \<and> locationChanged \<noteq> hash x2 i)"
              using STMap(2) TypedStoSubpref.simps(3)[of locationChanged x2 x1 struct]
              using TypedStoSubpref_sameLoc by auto
            ultimately show ?case using STMap(1) by auto
          next
            case (STValue x)
            then have c5:"(x2 \<noteq> locationChanged \<or> STValue t' \<noteq> STValue x)" using Subpref.simps(1)[of x x2 "STValue t'" locationChanged] by auto
            then show ?case
            proof(cases "x2 \<noteq> locationChanged")
              case True
              then have c10:"Storage st' (Address env) $$ x2 = Storage st (Address env) $$ x2" using subcase2 nonLocChanged by auto
              then have " SCon (STValue x) x2 (Storage st (Address env))" using STValue by blast
              then show ?thesis using c10
                by (simp add: accessStorage_def)
            next
              case False
              then have "x2 = locationChanged" by simp
              then have "STValue t' = STValue x" using subcase2 Storeloc inDen lexpStorage[of env st cd lv g locationChanged t' g'] f1 2(1) a20 a30
                by (metis STValue.prems(1) TypedStoSubpref.simps(1))
              then show ?thesis using False c5 by auto
            qed
          qed
        qed
        then show ?thesis
          using Storeloc a30 by auto
      qed
    qed
    then have "typeCompat (Denvalue env) (Stack st) (Memory st') (Storage st' (Address env)) cd" using subcase2 by auto
  next
    show "lessThanTopLocs cd" using 2 unfolding TypeSafe_def by simp
  next
    have "Memory st = Memory st'" using subcase2(4) by simp
    then show "lessThanTopLocs (Memory st')" using 2 unfolding TypeSafe_def by simp
  next
    have "envAddressesWellFormed env" using 2 unfolding TypeSafe_def by simp
    then show "addressFormat (Address env)" and "addressFormat (Sender env)" by simp+

  next
    show "AddressTypes (Accounts st')" using 2(1) unfolding TypeSafe_def using subcase2 by simp
  next
    have "Accounts st'= Accounts st" using subcase2 by auto
    then show "fullyInitialised env (Accounts st') (Stack st')" using 2(3) subcase2(4) unfolding fullyInitialised_def updateStore_def accessStore_def by auto
  next
    have cc0:"\<forall>l ptr_loc. accessStore l (Stack st') = Some (KMemptr ptr_loc) \<longrightarrow> accessStore l (Stack st) = Some (KMemptr ptr_loc)"
      using subcase2(4) unfolding updateStore_def accessStore_def by auto
    show "denvalueTypeCorrectness env (Stack st') (Memory st')"
      unfolding denvalueTypeCorrectness_def
    proof intros
      fix t l ptr_loc
      assume "(type.Memory t, Stackloc l) |\<in>| fmran (Denvalue env) \<and>
     accessStore l (Stack st') = Some (KMemptr ptr_loc)"
      then have "(case t of
       MTArray len arr \<Rightarrow> (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr)
       | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st) = Some (MTValue val))"
        using 2(1) unfolding TypeSafe_def denvalueTypeCorrectness_def using cc0 by blast
      moreover have "Memory st = Memory st'" using subcase2(4) by simp
      ultimately show "case t of
     MTArray len arr \<Rightarrow> (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr)
     | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st') = Some (MTValue val)"
        by metis
    qed
  next
    show "subPrefixStructuralConsistency (Memory st')"
      using 2(1) subcase2(4) unfolding TypeSafe_def by simp
  next
    show "SomeValSomeTyp (Memory st')" using 2(1) unfolding TypeSafe_def using subcase2(4) by simp
  next
    show "\<And>locs t. accessTypeStore locs (Memory st) = Some t \<Longrightarrow> accessTypeStore locs (Memory st') = Some t"
      using subcase2 by simp
  next
    show "\<And>locs v. accessStore locs (Memory st) = Some (MPointer v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MPointer v')"
      using subcase2 by simp
  next
    show "\<And>locs v. accessStore locs (Memory st) = Some (MValue v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MValue v')"
      using subcase2 by simp
  next
    show " \<And>i loc. i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<Longrightarrow> accessStore loc
        (Memory st) = None \<Longrightarrow> accessStore loc (Memory st') = None"
      using subcase2 by simp
  next
    show "Toploc (Memory st) \<le> Toploc (Memory st')" using subcase2 by simp
  qed
qed

text \<open>Assignment case 3: a value assigned to a memory location.\<close>

lemma TypeSafe_Assign_3:
  assumes "TypeSafe env (Accounts st) (Stack st) (Memory st) (Storage st) cd"
    and "stmt (ASSIGN lv ex) env cd st = Normal ((), st')"
    and "fullyInitialised env (Accounts st) (Stack st)"
    and "expr ex env cd (st\<lparr>state.Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>) (state.Gas st - costs (ASSIGN lv ex) env cd st) = Normal ((KValue v, Value t), g)"
    and "lexp lv env cd (st\<lparr>state.Gas := g\<rparr>) g = Normal((LMemloc l, type.Memory (MTValue t')),g')"
    and "convert t t' v = Some v'"
    and "st' = st\<lparr>state.Gas := g', Memory := updateStore l (MValue v') (Memory st)\<rparr>"
  shows "StateInvariant env st st' cd"
proof -
  let ?case = "StateInvariant env st st' cd"
  note 2 = assms(1-3)
  note 3 = assms(4-7)
  have sameStack:"Stack st' = Stack st" using 3(4) by auto
  have sameStorage:"Storage st' = Storage st " using 3 by auto
  have sameAccounts:"Accounts st = Accounts st'" using 3 by simp
  have temp:"TypeSafe env (Accounts (st\<lparr>Gas := g\<rparr>)) (Stack (st\<lparr>Gas := g\<rparr>)) (Memory (st\<lparr>Gas := g\<rparr>)) (Storage (st\<lparr>Gas := g\<rparr>)) cd"
    using 2(1) by simp
  have ttt:"fullyInitialised env (Accounts (st\<lparr>Gas := g\<rparr>)) (Stack (st\<lparr>Gas := g\<rparr>))" using 2(3) unfolding fullyInitialised_def by simp
  show ?thesis
  proof(cases rule:lexpIndexMem[OF 3(2) temp ttt])
    case lInfo:(1 x21 x22 tp tParent l' l'' prnt len' arr' i)

    have nonLocChanged:"\<forall>locs. locs \<noteq> l \<longrightarrow> accessStore locs (Memory st) = accessStore locs (Memory st')"
      using 3 unfolding updateStore_def accessStore_def by simp

    have TCsrc:"typeCon t (extractValueType (KValue v)) \<and> (\<exists>xx. KValue v = KValue xx)"
      using 2(1) 3(1) exprTypeconInduct(3)[of ex env cd "(st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)"
          "(state.Gas st - costs (ASSIGN lv ex) env cd st)" "KValue v" "Value t" g]
      using 2(3) unfolding fullyInitialised_def
      by (auto split:type.splits if_splits )


    obtain len subT where tParentType:"tParent = MTArray len subT" using lInfo by blast
    then have compType:"CompMemType (Memory (st\<lparr>Gas := g\<rparr>)) len subT (MTValue t') l'' l"
        and lsublocs:"l = hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<and> i < len' \<and> arr' = (MTValue t') \<and> MCon (MTArray len' arr') (Memory (st)) prnt"
        and lsublocs3:"(prnt = l'' \<and> len = len' \<and> arr' = subT \<or> CompMemType (Memory (st)) len subT (MTArray len' arr') l'' prnt)"
      using lInfo 3(3) by fastforce+

    then have lsublocs2:" CompMemType (Memory (st)) len' arr' (MTValue t') prnt l"
      using 3(3) CompMemType.simps(2) by auto
    then have bb9:"\<forall>subT subloc. CompMemType (Memory (st)) len' arr' subT prnt subloc \<and> subloc = l
                                \<longrightarrow> subT = (MTValue t')"
      using CompMemTypeSameLocsSameType lsublocs by blast

    have mconPrnt:"MCon (MTArray len' (MTValue t')) (Memory st) prnt" using lsublocs by auto
    have ldef:"l = hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<and> i < len'" using lsublocs by auto

    have t6:"(type.Memory tParent, Stackloc l') |\<in>| fmran (Denvalue env)" using lInfo by blast
    have t7:" MCon (MTArray len subT) (Memory (st)) l''" using lInfo
      using tParentType by auto
    then have mconlOld:"MCon (MTValue t') (Memory st) l" using 3(3) lInfo
      using CompTypeRemainsMCon lsublocs lsublocs2 by blast
    have "MCon (MTArray len' arr') (Memory st) prnt" using lsublocs3
      using lsublocs by blast
    then have mcPrntNew:"MCon (MTArray len' arr') (Memory st') prnt"
    proof -
      have lenNotZero:"len' \<noteq> 0" using lsublocs by auto
      have prntNotL:"prnt \<noteq> l" using ldef
        by (metis hash_inequality)
      then have p2:"(\<exists>p. accessStore prnt (Memory st') = Some (MPointer p)) \<or> accessStore prnt (Memory st') = None"
        using mconPrnt lenNotZero nonLocChanged by simp
      have "\<forall>i<len'.
          (case accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') of None \<Rightarrow> False
           | Some (MValue val) \<Rightarrow> (case arr' of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon arr' (Memory st') (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
           | Some (MPointer loc2) \<Rightarrow> (case arr' of MTArray len' arr'a \<Rightarrow> MCon arr' (Memory st') loc2 | MTValue Types \<Rightarrow> False))
         "
      proof(intros)
        fix i1 assume in1:"i1<len'"
        show "case accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) (Memory st') of None \<Rightarrow> False
        | Some (MValue val) \<Rightarrow> (case arr' of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon arr' (Memory st') (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i1)))
        | Some (MPointer loc2) \<Rightarrow> (case arr' of MTArray len' arr'a \<Rightarrow> MCon arr' (Memory st') loc2 | MTValue Types \<Rightarrow> False)"
        proof(cases "i1 = i")
          case True
          then have "(hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) = l" using ldef by simp
          then have ac:"accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) (Memory st') = Some((MValue v'))" using 3 by simp
          have "MCon (MTValue t') (Memory st) (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i1))"
            using \<open>hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i1) = l\<close> lsublocs mconlOld by auto
          then have "typeCon t' v'" unfolding MCon.simps
            by (metis "3"(3) TCsrc convertSame extractValueType.simps(1) typeSafeConvert)
          then show ?thesis
            by (simp add: \<open>accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) (Memory st') = Some (MValue v')\<close> lsublocs)
        next
          case False
          then have sameAC:"accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) (Memory st') = accessStore (hash prnt
              (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) (Memory st)" using ldef nonLocChanged in1
            by (metis Read_Show_nat'_id hash_never_equal_suffix)
          then obtain ptr where ptrDef:"accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) (Memory st) = Some (MValue ptr)" using in1
            using lsublocs MCon_sub_MTVal_imps_val by blast
          then have ptrMC:"case accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) of None \<Rightarrow> False | Some
              (MValue xa) \<Rightarrow> typeCon t' xa | Some (MPointer t) \<Rightarrow> False"
            using in1 mconPrnt unfolding MCon.simps
            using lsublocs mconlOld MCon.simps(1) by blast
          then show ?thesis using sameAC
            using in1 lsublocs ptrDef by force
        qed
      qed
      then show ?thesis using lenNotZero p2 by simp
    qed

    have "(type.Memory (MTArray len subT), Stackloc l') |\<in>| fmran (Denvalue env) \<and> accessStore l' (Stack st) = Some (KMemptr l'')"
      using lInfo(2,3,4) tParentType by simp


    have cmpO_imps_new:"\<forall>x11 x12 stl2 dt prnt. CompMemType (Memory st) x11 x12 dt stl2 prnt
          \<longrightarrow> CompMemType (Memory st') x11 x12 dt stl2 prnt"
    proof intros
      fix x11 x12 stl2 dt prnt
      assume "CompMemType (Memory st) x11 x12 dt stl2 prnt"
      then show "CompMemType (Memory st') x11 x12 dt stl2 prnt"
      proof(induction x12 arbitrary:x11 stl2)
        case (MTArray x1 x12)
        then obtain ii ll where iiDef: "ii<x11 \<and> accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) (Memory st) = Some (MPointer ll)
                  \<and> (ll = prnt \<and> MTArray x1 x12 = dt \<or> CompMemType (Memory st) x1 x12 dt ll prnt)"
          unfolding CompMemType.simps by blast
        then show ?case
        proof(cases "ll = prnt")
          case True
          then show ?thesis using MTArray.prems iiDef
            by (metis MCon_sub_MTVal_imps_val MTArray.IH memoryvalue.distinct(1) lsublocs nonLocChanged option.inject CompMemType.simps(2))
        next
          case False
          then show ?thesis
            by (metis MCon_sub_MTVal_imps_val MTArray.IH memoryvalue.distinct(1) iiDef lsublocs nonLocChanged option.inject CompMemType.simps(2))
        qed
      next
        case (MTValue x)
        then show ?case unfolding CompMemType.simps by simp
      qed

    qed

    have nToO_neg:"\<forall>x11 x12 stl2 prnt . \<not>TypedMemSubPrefPtrs (Memory st') x11 x12 stl2 prnt \<longrightarrow> \<not>TypedMemSubPrefPtrs (Memory st) x11 x12 stl2 prnt"
    proof intros
      fix x11 x12 stl2 prnt
      assume in1:"\<not> TypedMemSubPrefPtrs (Memory st') x11 x12 stl2 prnt"
      show "\<not> TypedMemSubPrefPtrs (Memory st) x11 x12 stl2 prnt"
      proof
        assume in2:"TypedMemSubPrefPtrs (Memory st) x11 x12 stl2 prnt"
        then show False using in1
        proof(induction x12 arbitrary:x11 stl2)
          case (MTArray x1 x12)
          then obtain ii ll where iiDef:"ii<x11 \<and> accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) (Memory st) = Some
              (MPointer ll) \<and> (ll = prnt \<or> TypedMemSubPrefPtrs (Memory st) x1 x12 ll prnt)"
            unfolding TypedMemSubPrefPtrs.simps by blast
          then show ?case
          proof(cases "ll = prnt")
            case True
            then have "(hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) \<noteq> l" using iiDef mconlOld by auto
            then show ?thesis using True iiDef nonLocChanged
              using MTArray.prems(2) by auto
          next
            case False
            then show ?thesis using MTArray iiDef
              by (metis MCon_sub_MTVal_imps_val memoryvalue.distinct(1) lsublocs nonLocChanged option.inject TypedMemSubPrefPtrs.simps(2))
          qed
        next
          case (MTValue x)
          then show ?case by simp
        qed
      qed
    qed


    have nToO:"\<forall>len2 arr2 stl2 stl1. TypedMemSubPrefPtrs (Memory st') len2 arr2 stl2 stl1 \<longrightarrow> TypedMemSubPrefPtrs (Memory st) len2 arr2 stl2 stl1"
    proof intros
      fix len2 arr2 stl2 stl1
      assume "TypedMemSubPrefPtrs (Memory st') len2 arr2 stl2 stl1"
      then show "TypedMemSubPrefPtrs (Memory st) len2 arr2 stl2 stl1 "
      proof(induction arr2 arbitrary:len2 stl2)
        case (MTArray x1 arr2)
        then obtain ii ll where iidef:"ii<len2 \<and> accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) (Memory st') = Some (MPointer ll) \<and>
                                   (ll = stl1 \<or> TypedMemSubPrefPtrs (Memory st') x1 arr2 ll stl1)"
          unfolding TypedMemSubPrefPtrs.simps by auto
        then show ?case
        proof(cases "ll = stl1")
          case True
          then show ?thesis
            by (metis MCon_sub_MTVal_imps_val memoryvalue.distinct(1) iidef lsublocs mcPrntNew nonLocChanged option.inject TypedMemSubPrefPtrs.simps(2))
        next
          case False
          then show ?thesis
            by (metis MCon_sub_MTVal_imps_val MTArray.IH memoryvalue.distinct(1) iidef lsublocs mcPrntNew nonLocChanged option.inject TypedMemSubPrefPtrs.simps(2))
        qed
      next
        case (MTValue x)
        then show ?case by simp
      qed
    qed


    have mcl:"MCon (MTValue t') (Memory st') l" using mconlOld 3(4)
      using CompTypeRemainsMCon cmpO_imps_new lsublocs2 mcPrntNew by blast

    show ?thesis unfolding TypeSafe_def StateInvariant_def
    proof intros
      show "AddressTypes (Accounts st')" using 2(1) 3 unfolding TypeSafe_def by simp
    next
      show "unique_locations (Denvalue env)" using 2(1) unfolding TypeSafe_def by simp
    next
      have a0:" compPointers (Stack st) (Denvalue env)" using 2(1) unfolding TypeSafe_def by blast
      then show "compPointers (Stack st') (Denvalue env)" using sameStack sameStorage by simp
    next
      show "safeContract (Accounts st') (Storage st')" using sameStorage sameAccounts using 2(1) unfolding TypeSafe_def safeContract_def by auto
    next
      show "balanceTypes (Accounts st')" using 3 using 2(1) unfolding TypeSafe_def by simp
    next
      have "envAddressesWellFormed env" using 2(1) unfolding TypeSafe_def by simp
      then show "addressFormat (Address env)" and "addressFormat (Sender env)" by simp+
    next
      show "svalueTypes (Svalue env)" using 2(1) unfolding TypeSafe_def by simp
    next
      have *:"((\<forall>tloc loc. Toploc (Stack st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Stack st) = None) \<and>
            (\<forall>loc y. accessStore loc (Stack st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Stack st). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))) "
        using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by simp
      have **:"Toploc (Stack st) = Toploc (Stack st')" using 3 unfolding updateStore_def by auto
      show "lessThanTopLocs (Stack st')" unfolding lessThanTopLocs_def
      proof intros

        fix tloc loc
        assume h1:"Toploc (Stack st') \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
        then have "Toploc (Stack st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)" using ** by simp
        then show "accessStore loc (Stack st') = None" using *
          by (simp add: sameStack)
      next
        fix loc y
        assume h1:" accessStore loc (Stack st') = Some y"
        then show "\<exists>tloc<Toploc (Stack st'). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)" using ** *
          by (metis sameStack)
      qed
    next
      show "lessThanTopLocs cd" using 2(1) unfolding TypeSafe_def by simp
    next
      have a12:"Toploc (Memory st) = Toploc (Memory st')" using 3 unfolding updateStore_def by auto
      have a15:"lessThanTopLocs (Memory st)" using 2 unfolding TypeSafe_def by simp
      have tloc:"Toploc (Memory st) < Toploc (snd (allocate (Memory st)))" unfolding allocate_def by simp
      show "lessThanTopLocs (Memory st')" unfolding lessThanTopLocs_def
      proof intros
        fix tloc loc
        assume b10: "Toploc (Memory st') \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
        then have b20:"Toploc (Memory st) \<le> tloc" using a12 tloc a12
          by force

        then show "accessStore loc (Memory st') = None "
          by (metis MCon_imps_Some a15 b10 lessThanSome_imps_Locs lessThanSome_imps_Locs_hash lessThanTopLocs_def linorder_not_less mconlOld nonLocChanged)
      next
        fix loc y
        assume "accessStore loc (Memory st') = Some y "
        then show "\<exists>tloc<Toploc (Memory st'). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
          by (metis MConAccessSame.simps(1) SameMCon_imps_MConAccessSame a12 a15 lessThanTopLocs_def mconlOld nonLocChanged)
      qed
    next
      show "typeCompat (Denvalue env) (Stack st') (Memory st') (Storage st' (Address env)) cd"
        unfolding typeCompat_def
      proof intros
        fix tLook lLook
        assume inDen:" (tLook, lLook) |\<in>| fmran (Denvalue env)"
        show " denvalueCon (Stack st') (Memory st') (Storage st' (Address env)) cd tLook lLook"
        proof(cases lLook)
          case (Stackloc x1)
          then show ?thesis
          proof(cases "accessStore x1 (Stack st')")
            case None
            then show ?thesis using 2(1) unfolding TypeSafe_def typeCompat_def using sameStorage inDen sameStack Stackloc by force
          next
            case (Some a)
            then show ?thesis
            proof(cases a)
              case (KValue x1')
              then show ?thesis using 2(1) unfolding TypeSafe_def typeCompat_def using sameStorage inDen sameStack Stackloc Some by force
            next
              case (KCDptr x2)
              then show ?thesis using 2(1) unfolding TypeSafe_def typeCompat_def using sameStorage inDen sameStack Stackloc Some by force
            next
              case (KMemptr x3)
              then obtain struct where stT: "tLook = type.Memory struct" using 2(1) unfolding TypeSafe_def typeCompat_def using sameStorage inDen sameStack Stackloc Some
                by (cases tLook; fastforce)
              have structss:"(case struct of
     MTArray len arr \<Rightarrow>
       (\<forall>i<len. accessTypeStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr)
     | MTValue val \<Rightarrow> accessTypeStore x3 (Memory st) = Some (MTValue val))"
                using 2(1) inDen KMemptr Some Stackloc stT 3(4)
                unfolding TypeSafe_def denvalueTypeCorrectness_def by simp
              then have structss:"(case struct of
     MTArray len arr \<Rightarrow>
       (\<forall>i<len. accessTypeStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr)
     | MTValue val \<Rightarrow> accessTypeStore x3 (Memory st) = Some (MTValue val))"
                by (metis (no_types, lifting) )
              have mcold:"MCon struct (Memory st) x3" using stT
                by (metis 2(1) KMemptr Some Stackloc inDen sameMemTSafe sameStack)
              then have "MCon struct (Memory st') x3" using structss
              proof(induction struct arbitrary:x3)
                case (MTArray x11 x12)
                have oldexp:"(\<forall>i<x11.
                      case accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) of None \<Rightarrow> False
                      | Some (MValue val) \<Rightarrow>
                          (case x12 of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon x12 (Memory st) (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
                      | Some (MPointer loc2) \<Rightarrow>
                          (case x12 of MTArray len' arr' \<Rightarrow> MCon x12 (Memory st) loc2 | MTValue val \<Rightarrow> False)) \<and>
                  (\<exists>p. accessStore x3 (Memory st) = Some (MPointer p) \<or> accessStore x3 (Memory st) = None)"
                  using MTArray.prems(1) unfolding MCon.simps by simp
                then have notL:"x3 \<noteq> l" using lInfo(7) by auto
                then have conc1:"(\<exists>p. accessStore x3 (Memory st') = Some (MPointer p) \<or> accessStore x3 (Memory st') = None)"
                  using 3(4) oldexp unfolding accessStore_def updateStore_def by simp

                then have subs:"(\<forall>i<x11. accessTypeStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some x12)"
                  using structss MTArray by simp

                have "(\<forall>i<x11.
                      case accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') of None \<Rightarrow> False
                      | Some (MValue val) \<Rightarrow>
                          (case x12 of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon x12 (Memory st') (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
                      | Some (MPointer loc2) \<Rightarrow>
                          (case x12 of MTArray len' arr' \<Rightarrow> MCon x12 (Memory st') loc2 | MTValue val \<Rightarrow> False))"
                proof(intros)
                  fix i assume idef:"i<x11"
                  then consider (val1) val typw where "accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some (MValue val)
                                          \<and> x12 = MTValue typw
                                          \<and> MCon x12 (Memory st) (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i))"
                    | (ptr1) ptr l1 a1 where "accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some (MPointer ptr)
                                        \<and> x12 = MTArray l1 a1
                                        \<and> MCon x12 (Memory st) ptr"
                    using oldexp
                    by (metis MCon_imps_sub_Mcon MTArray.prems(1) mtypes.distinct(1) gr_implies_not0 mcon_accessStore nat_neq_iff)
                  then show "case accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') of None \<Rightarrow> False
       | Some (MValue val) \<Rightarrow> (case x12 of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon x12 (Memory st') (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
       | Some (MPointer loc2) \<Rightarrow> (case x12 of MTArray len' arr' \<Rightarrow> MCon x12 (Memory st') loc2 | MTValue val \<Rightarrow> False)"
                  proof(cases)
                    case val1
                    then show ?thesis
                    proof(cases "(hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) = l")
                      case True
                      then have "x12 = (MTValue t')" using subs lInfo(6) idef by auto
                      then show ?thesis using 3(4) True
                        unfolding updateStore_def accessStore_def using idef mcl by simp
                    next
                      case False
                      then have sameACC:"accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st')"
                        using 3(4)unfolding updateStore_def accessStore_def by simp
                      then have "MCon x12 (Memory st') (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i))"
                        using val1 unfolding MCon.simps by auto
                      then show ?thesis using val1 sameACC by simp
                    qed
                  next
                    case ptr1
                    then have notl:"(hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) \<noteq> l" using mconlOld unfolding MCon.simps by auto

                    have " case x12 of MTArray len arr \<Rightarrow>
    (\<forall>i<len. accessTypeStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr)
  | MTValue val \<Rightarrow> accessTypeStore ptr (Memory st) = Some (MTValue val)"
                      using 2(1) unfolding TypeSafe_def subPrefixStructuralConsistency_def using MTArray.prems
                      using ptr1 idef by fastforce
                    then have "MCon x12 (Memory st') ptr"
                      using MTArray.IH[of ptr] ptr1 by blast
                    then show ?thesis using ptr1 notl 3(4) unfolding accessStore_def updateStore_def by simp
                  qed
                qed
                then show ?case using conc1 MTArray.prems(1) unfolding MCon.simps by simp
              next
                case (MTValue x2)
                then show ?case
                proof(cases "x3 = l")
                  case True
                  then have "x2 = t'" using lInfo(6) structss MTValue by simp
                  then show ?thesis using lInfo MTValue True
                    using CompTypeRemainsMCon cmpO_imps_new lsublocs2 mcPrntNew by blast
                next
                  case False
                  then have "accessStore x3 (Memory st) = accessStore x3 (Memory st')"
                    using 3(4) unfolding updateStore_def accessStore_def by simp
                  then show ?thesis using mcold MTValue unfolding MCon.simps by simp
                qed
              qed

              then show ?thesis using sameStorage inDen sameStack Stackloc Some KMemptr stT by simp
            next
              case (KStoptr x4)
              then show ?thesis using 2(1) unfolding TypeSafe_def typeCompat_def using sameStorage inDen sameStack Stackloc Some by (cases tLook; force)
            qed
          qed
        next
          case (Storeloc x2)
          then show ?thesis using 2(1) unfolding TypeSafe_def typeCompat_def using sameStorage inDen
            by (metis denvalue.simps(6))
        qed
      qed
      then have "typeCompat (Denvalue env) (Stack st) (Memory st') (Storage st' (Address env)) cd" using sameStack by auto
    next
      have "Accounts st'= Accounts st" using 3 by auto
      then show "fullyInitialised env (Accounts st') (Stack st')" using 2(3) 3 unfolding fullyInitialised_def by auto
    next

      have sameStack:"Stack st = Stack st'" using 3 by simp
      have oldL:"\<exists>v''. accessStore l (Memory (st\<lparr>Gas := g\<rparr>)) = Some (MValue v'')" using lInfo
        using MCon_sub_MTVal_imps_val by blast
    next
      have cc0:"\<forall>l ptr_loc. accessStore l (Stack st') = Some (KMemptr ptr_loc) \<longrightarrow> accessStore l (Stack st) = Some (KMemptr ptr_loc)"
        using 3(4) unfolding updateStore_def accessStore_def by auto
      have cc1:"\<forall>locs. accessTypeStore locs (Memory st) = accessTypeStore locs (Memory st')"
        using 3(4) unfolding updateStore_def accessTypeStore_def by simp
      show "denvalueTypeCorrectness env (Stack st') (Memory st')"
        unfolding denvalueTypeCorrectness_def
      proof intros
        fix t l ptr_loc sub_loc
        assume "(type.Memory t, Stackloc l) |\<in>| fmran (Denvalue env) \<and>
     accessStore l (Stack st') = Some (KMemptr ptr_loc)"
        then have old:"(
      (case t of MTArray len arr \<Rightarrow> (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr)
       | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st) = Some (MTValue val)))"
          using 2(1) unfolding TypeSafe_def denvalueTypeCorrectness_def using cc0 by blast

        then show "case t of MTArray len arr \<Rightarrow> (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr)
     | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st') = Some (MTValue val)"

        proof(cases t)
          case (MTArray x11 x12)
          then have o2:" \<forall>i<x11. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some x12"
            using old by simp
          then have conc1:"(\<forall>i<x11. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some x12)" using cc1 by simp
          then show ?thesis using MTArray cc1 old 3(4) by auto
        next
          case (MTValue x2)
          then show ?thesis using cc1 old by simp
        qed
      qed
    next
      have cc1:"\<forall>locs. accessTypeStore locs (Memory st) = accessTypeStore locs (Memory st')"
        using 3(4) unfolding updateStore_def accessTypeStore_def by simp
      have old:"(\<forall>locs. (\<exists>t. accessStore locs (Memory st) = Some t) = (\<exists>tt. accessTypeStore locs (Memory st) = Some tt))"
        using 2(1) unfolding TypeSafe_def SomeValSomeTyp_def by blast
      show "SomeValSomeTyp (Memory st')" unfolding SomeValSomeTyp_def
      proof intros
        fix locs
        show "(\<exists>t. accessStore locs (Memory st') = Some t) = (\<exists>tt. accessTypeStore locs (Memory st') = Some tt) "
        proof(cases "locs = l")
          case True
          then have "accessStore locs (Memory st') = Some (MValue v')"
            using 3 unfolding updateStore_def accessStore_def by simp
          moreover have "\<exists>v. accessStore locs (Memory st) = Some v "
            using mconlOld True old by auto
          ultimately show ?thesis using old cc1 by simp
        next
          case False
          then have "accessStore locs (Memory st) = accessStore locs (Memory st')"
            using 3 unfolding updateStore_def accessStore_def by simp
          then show ?thesis using cc1 old by metis
        qed
      qed

    next
      have old:"subPrefixStructuralConsistency (Memory st)"
        using 2(1) unfolding TypeSafe_def by blast
      show "subPrefixStructuralConsistency (Memory st')"
        unfolding subPrefixStructuralConsistency_def
      proof intros
        fix locs tp
        assume in1:"accessTypeStore locs (Memory st') = Some tp"
        have allTyp:"\<forall>locs. accessTypeStore locs (Memory st) = accessTypeStore locs (Memory st')"
          using 3 unfolding updateStore_def accessTypeStore_def by auto
        have notNo:"accessStore locs (Memory st) \<noteq> None"
        proof -
          have "accessTypeStore locs (Memory st) = Some tp"
            using in1 allTyp by simp
          then have "\<exists>v. accessStore locs (Memory st) = Some v"
            using 2(1) unfolding TypeSafe_def SomeValSomeTyp_def by simp
          then show ?thesis by simp
        qed
        then have old':"(case accessStore locs (Memory st) of Some (MValue v) \<Rightarrow>
          \<exists>val. MCon tp (Memory st) locs \<and> tp = MTValue val \<and> accessTypeStore locs (Memory st) = Some tp
      | Some (MPointer p) \<Rightarrow>
          \<exists>len arr.
             MCon tp (Memory st) p \<and>
             tp = MTArray len arr \<and> (\<forall>i<len. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr))"
          using old in1 allTyp unfolding subPrefixStructuralConsistency_def by fastforce
        then consider (val) v val' where "accessStore locs (Memory st) = Some (MValue v)
                                          \<and> MCon tp (Memory st) locs \<and> tp = MTValue val'
                                          \<and> accessTypeStore locs (Memory st) = Some tp"
          | (ptr) p len arr where "accessStore locs (Memory st) = Some (MPointer p) \<and>
                                   MCon tp (Memory st) p \<and> tp = MTArray len arr \<and>
                                   (\<forall>i<len. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr)"
          using notNo by (auto split:option.splits memoryvalue.splits)

        then show "case accessStore locs (Memory st') of None \<Rightarrow> False
     | Some (MValue v) \<Rightarrow>
         \<exists>val. MCon tp (Memory st') locs \<and> tp = MTValue val \<and> accessTypeStore locs (Memory st') = Some tp
     | Some (MPointer p) \<Rightarrow>
         \<exists>len arr.
            MCon tp (Memory st') p \<and>
            tp = MTArray len arr \<and> (\<forall>i<len. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr)"
        proof(cases)
          case val
          then show ?thesis
          proof(cases "locs = l")
            case True
            then have "tp = (MTValue t')" using lInfo(6) allTyp in1 by simp
            moreover have "\<exists>v''. accessStore locs (Memory st') = Some (MValue v'')"
              using True mcl MCon_sub_MTVal_imps_val lsublocs mcPrntNew by presburger
            ultimately show ?thesis using mcl lInfo(6) allTyp val True by fastforce
          next
            case False
            then show ?thesis using val nonLocChanged allTyp by auto
          qed
        next
          case ptr
          then have notlLocs:"locs \<noteq> l"
            using mconlOld by force
          have cc1:"(\<forall>i<len. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr)"
            using ptr allTyp by simp
          have "MCon (MTArray len arr) (Memory st) p" using ptr by blast

          then have "MCon (MTArray len arr) (Memory st') p" using cc1
          proof(induction arr arbitrary:len p)
            case (MTArray x11 x12)
            have oldexp:"(\<forall>i<len. \<exists>val.
       accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some (MPointer val) \<and>
           MCon (MTArray x11 x12) (Memory st) val)"
              using MTArray.prems(1) MCon.simps(2)[of len "MTArray x11 x12" "Memory st" p]
              by (meson CompMemType.simps(2) CompTypeRemainsMCon MConArrayPointers)


            then have subs:"\<forall>i<len. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some (MTArray x11 x12)"
              using MTArray by simp

            have "(\<forall>i<len. \<exists>val.
       accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some (MPointer val) \<and>
           (MCon (MTArray x11 x12) (Memory st') (val)))"
            proof(intros)
              fix i assume idef:"i<len"

              then show "\<exists>val. accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some (MPointer val) \<and>
                          MCon (MTArray x11 x12) (Memory st') val"
              proof(cases "(hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) = l")
                case True
                then show ?thesis using mconlOld oldexp idef by auto
              next
                case False
                then have sameACC:"accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st')"
                  using 3(4)unfolding updateStore_def accessStore_def by simp
                then obtain val where mcc:"accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some (MPointer val)
                                      \<and> MCon (MTArray x11 x12) (Memory st) val"
                  using oldexp unfolding MCon.simps using idef by blast
                then have "accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some (MPointer val) "
                  using sameACC by simp
                have "\<forall>i<x11. accessTypeStore (hash val (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some x12"
                  using 2(1) subs allTyp idef mcc unfolding TypeSafe_def subPrefixStructuralConsistency_def
                  by force
                then have "MCon (MTArray x11 x12) (Memory st') val"
                  using MTArray.IH[of x11 val] mcc idef allTyp by simp
                then show ?thesis using mcc sameACC idef oldexp by simp
              qed
            qed

            moreover have "(\<exists>p'. accessStore p (Memory st') = Some (MPointer p') \<or> accessStore p (Memory st') = None)"
            proof -
              have "p \<noteq> l" using mconlOld MTArray.prems(1) MCon.simps(2)[of len _ "Memory st" p] by auto
              then show ?thesis using nonLocChanged MTArray.prems(1) MCon.simps(2)[of len _ "Memory st" p] by simp
            qed
            moreover have "0 < len" using MTArray.prems(1) MCon.simps(2)[of len _ "Memory st" p] by simp
            ultimately show ?case using nonLocChanged MCon.simps(2)[of len _ "Memory st'" p] by auto
          next
            case (MTValue x2)
            have oldexp:"(\<forall>i<len. \<exists>val.
       accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some (MValue val) \<and>
           (MCon (MTValue x2) (Memory st) (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i))))"
              using MTValue.prems(1) MCon.simps(2)[of len "MTValue x2" "Memory st" p]
              by (auto split:option.splits memoryvalue.splits mtypes.splits)

            then have subs:"\<forall>i<len. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some (MTValue x2)"
              using MTValue by simp


            have "(\<forall>i<len. \<exists>val.
       accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some (MValue val) \<and>
           (MCon (MTValue x2) (Memory st') (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i))))"
            proof(intros)
              fix i assume idef:"i<len"

              then show "\<exists>val. accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some (MValue val) \<and>
                               MCon (MTValue x2) (Memory st') (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i))"
              proof(cases "(hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) = l")
                case True
                then have "(MTValue x2) = (MTValue t')" using subs lInfo(6) idef allTyp by auto
                then show ?thesis using 3(4) True
                  unfolding updateStore_def accessStore_def using idef mcl by simp
              next
                case False
                then have sameACC:"accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st')"
                  using 3(4)unfolding updateStore_def accessStore_def by simp
                then have "MCon (MTValue x2) (Memory st') (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i))"
                  using oldexp unfolding MCon.simps
                  using idef by force
                then show ?thesis using sameACC idef oldexp by metis
              qed
            qed

            moreover have "(\<exists>p'. accessStore p (Memory st') = Some (MPointer p') \<or> accessStore p (Memory st') = None)"
            proof -
              have "p \<noteq> l" using mconlOld MTValue(1) MCon.simps(2)[of len "MTValue x2" "Memory st" p] by auto
              then show ?thesis using nonLocChanged MTValue(1) MCon.simps(2)[of len "MTValue x2" "Memory st" p] by simp
            qed
            moreover have "0 < len" using MTValue(1) MCon.simps(2)[of len "MTValue x2" "Memory st" p] by simp
            ultimately show ?case using nonLocChanged MCon.simps(2)[of len "MTValue x2" "Memory st'" p] by auto
          qed
          then show ?thesis using ptr nonLocChanged notlLocs allTyp by auto
        qed
      qed
    next
      show "\<And>locs t. accessTypeStore locs (Memory st) = Some t \<Longrightarrow> accessTypeStore locs (Memory st') = Some t"
        using 3(4) unfolding updateStore_def accessTypeStore_def by simp
    next
      show "\<And>locs v. accessStore locs (Memory st) = Some (MPointer v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MPointer v')"
        using 3(4)
        by (metis MConAccessSame.simps(1) memoryvalue.distinct(1) SameMCon_imps_MConAccessSame mconlOld nonLocChanged option.inject)
    next
      show "\<And>locs v. accessStore locs (Memory st) = Some (MValue v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MValue v')"
        by (metis MCon_sub_MTVal_imps_val lInfo(7) mcPrntNew nonLocChanged)
    next
      show " \<And>i loc. i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<Longrightarrow> accessStore loc
          (Memory st) = None \<Longrightarrow> accessStore loc (Memory st') = None"
        by (metis MCon_sub_MTVal_imps_val accessStore_def fmdom_notI fmlookup_dom_iff lsublocs nonLocChanged)
    next
      have a12:"Toploc (Memory st) = Toploc (Memory st')" using 3 unfolding updateStore_def by auto
      then show "Toploc (Memory st) \<le> Toploc (Memory st')" by simp
    qed
  qed
qed

text \<open>Assignment case 4: a calldata array assigned to a memory variable on the stack: the array is copied into fresh memory.\<close>

lemma TypeSafe_Assign_4:
  assumes "TypeSafe env (Accounts st) (Stack st) (Memory st) (Storage st) cd"
    and "stmt (ASSIGN lv ex) env cd st = Normal ((), st')"
    and "fullyInitialised env (Accounts st) (Stack st)"
    and "expr ex env cd (st\<lparr>state.Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>) (state.Gas st - costs (ASSIGN lv
        ex) env cd st) = Normal ((KCDptr p, Calldata (MTArray x t)), g)"
    and "lexp lv env cd (st\<lparr>state.Gas := g\<rparr>) g = Normal((LStackloc l, type.Memory t'),g')"
    and "(MTArray x t) =t'"
    and "accessStore l (Stack st) = Some (KMemptr p')"
    and "(updateStore l (KMemptr (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))) (Stack st)) = st''"
    and "cpm2m p (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) x t cd (snd (allocate (Memory st))) = Some m"
    and "st' = st\<lparr>state.Gas := g', Memory := m, Stack := st''\<rparr>"
  shows "StateInvariant env st st' cd"
proof -
  let ?case = "StateInvariant env st st' cd"
  note 2 = assms(1-3)
  note 4 = assms(4-10)
  have nonChangedStack:"\<forall>loc. loc \<noteq> l \<longrightarrow> accessStore loc (Stack st) = accessStore loc (Stack st')" using 4 unfolding accessStore_def updateStore_def by auto
  have accessLStack:"accessStore l (Stack st') = Some (KMemptr (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))))" using 4 unfolding accessStore_def updateStore_def by auto
  have sameStorage:"Storage st' = Storage st " using 4 by auto
  have lInDen:"(type.Memory t', Stackloc l) |\<in>| fmran (Denvalue env)" using lexpStackloc_imps_inDen[of lv env cd _ _ l ] 4(2) by simp
  have nonLocChanged:"\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow> accessStore locs (snd (allocate (Memory st))) = accessStore locs m"
    using 4(6) unfolding cpm2m_def using cpm2mSingleChange[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd " (snd
        (allocate (Memory st)))" x m ] cpm2m_def[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" x t cd " (snd (allocate
        (Memory st)))" ]
    by fastforce
  have a30:"\<forall>locs. \<not> TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x t)
      \<longrightarrow> accessStore locs (snd (allocate (Memory st))) = accessStore locs m"
    using 4(6) unfolding cpm2m_def using cpm2mSingleChange_typedPref[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd " (snd (allocate (Memory st)))" x m ] by fastforce
  have selfPoint:"\<forall>l l'. TypedMemSubPref l (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x t) \<and> accessStore l m = Some (MPointer l') \<longrightarrow> l' = l"
    using 4(6) unfolding cpm2m_def using cpm2mSelfPointers[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd " (snd (allocate (Memory st)))" x m ] by blast
  have mInStd:"m = Memory st'" using 4 by simp

  have p'MCon:"MCon t' (Memory st) p'" using 2 4(4) unfolding TypeSafe_def typeCompat_def using lInDen by (auto split:denvalue.splits option.splits stackvalue.splits type.splits)

  have MConsrc:"MCon (MTArray x t) cd (extractValueType (KCDptr p)) \<and> (\<exists>xx. KCDptr p = KCDptr xx) \<and>
          (\<exists>stloc tp'' pa.
          (Calldata tp'', Stackloc stloc) |\<in>| fmran (Denvalue env) \<and>
          accessStore stloc (Stack (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)) = Some (KCDptr pa) \<and>
          (tp'' = (MTArray x t) \<and> KCDptr p = KCDptr pa \<or>
           (\<exists>len arr. extractValueType (KCDptr p) \<noteq> pa \<and> tp'' = MTArray len arr \<and> CompMemType cd len arr (MTArray x t) pa (extractValueType (KCDptr p)))))"
    using 2(1) 4(1) exprTypeconInduct(3)[of ex env cd "(st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)"
        "(state.Gas st - costs (ASSIGN lv ex) env cd st)" "KCDptr p" "Calldata (MTArray x t)" g]
      2(3) unfolding fullyInitialised_def by (auto split:type.splits if_splits )
  have "(\<exists>p. accessStore p' (Memory st) = Some (MPointer p)) \<or> accessStore p' (Memory st) = None" using p'MCon 4(3)
    by (metis MCon.simps(2))
  note limitSt1 = TypeSafe_memory_bounds(1)[OF 2(1)]
  note limitSt = TypeSafe_memory_bounds(2)[OF 2(1)]
  moreover have allocateSame:"\<forall>loc. accessStore loc (Memory st) = accessStore loc (snd (allocate (Memory st)))" using allocateSameAccess by blast
  ultimately have "accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (snd (allocate (Memory st))) = None" using LSubPrefL2_def by auto
  then have MCondest:" MCon (MTArray x t) m (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" using 4(6) unfolding cpm2m_def
    using MCon_cpm2m[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd "(snd (allocate (Memory st)))" x m] MConsrc extractValueType.simps(2) by metis
  have selfPoint2:"\<forall>l l'. LSubPrefL2 l (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> accessStore l (Memory st') =
      Some (MPointer l') \<longrightarrow> l' = l" using selfPoint limitSt1 limitSt
      "4"(6) a30 cpm2m_iter_dest_unchanged allocateSameAccess cpm2m_def eq_imp_le hash_inequality not_Some_eq
    by (metis mInStd)

  have stackDenvalLimits:"\<forall>struct loc stloc. (type.Memory struct, Stackloc loc) |\<in>| fmran (Denvalue env)
                          \<and> accessStore loc (Stack st) = Some (KMemptr stloc) \<longrightarrow> \<not> LSubPrefL2 stloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))"
    using typeSafe_noDenElementOverToploc_mem[OF 2(1)] by auto

  show ?thesis unfolding TypeSafe_def StateInvariant_def
  proof intros
    show "AddressTypes (Accounts st')" using 2(1) 4 unfolding TypeSafe_def by simp
  next
    show "unique_locations (Denvalue env)" using 2(1) unfolding TypeSafe_def by simp
  next
    have a0:" compPointers (Stack st) (Denvalue env)" using 2(1) unfolding TypeSafe_def by blast
    show "compPointers (Stack st') (Denvalue env)"
      using compPointers_stack_update[OF a0 nonChangedStack accessLStack] .
  next
    have "Accounts st = Accounts st'" using 4 by simp
    then show "safeContract (Accounts st') (Storage st')" using sameStorage using 2(1) unfolding TypeSafe_def safeContract_def by auto
  next
    show "balanceTypes (Accounts st')" using 4 using 2(1) unfolding TypeSafe_def by simp
  next
    have "envAddressesWellFormed env" using 2(1) unfolding TypeSafe_def by simp
    then show "addressFormat (Address env)" and "addressFormat (Sender env)" by simp+
  next
    show "svalueTypes (Svalue env)" using 2(1) unfolding TypeSafe_def by simp
  next
    have *:"((\<forall>tloc loc. Toploc (Stack st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Stack st) = None) \<and>
            (\<forall>loc y. accessStore loc (Stack st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Stack st). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))) "
      using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by simp
    have **:"Toploc (Stack st) = Toploc (Stack st')" using 4 unfolding updateStore_def by auto
    show "lessThanTopLocs (Stack st')" unfolding lessThanTopLocs_def
    proof intros

      fix tloc loc
      assume h1:"Toploc (Stack st') \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
      then have "Toploc (Stack st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)" using ** by simp
      then show "accessStore loc (Stack st') = None" using *
        by (metis "4"(4) nonChangedStack not_None_eq)
    next
      fix loc y
      assume h1:" accessStore loc (Stack st') = Some y"
      then show "\<exists>tloc<Toploc (Stack st'). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)" using ** *
        by (metis "4"(4) nonChangedStack)
    qed
  next
    show "lessThanTopLocs cd" using 2(1) unfolding TypeSafe_def by simp
  next
    have a10:"Toploc (snd (allocate (Memory st))) = Toploc m" using cpm2mTopLocSame[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory
        st)))" t cd "(snd (allocate (Memory st)))" x m] 4(6) mInStd unfolding cpm2m_def by fastforce
    have a15:"lessThanTopLocs (Memory st)" using 2 unfolding TypeSafe_def by simp
    have a20:"\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow> accessStore locs (snd (allocate (Memory st))) = accessStore locs m"
      using 4(6) unfolding cpm2m_def using cpm2mSingleChange[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd "(snd (allocate (Memory st)))" x m ]
        cpm2m_def[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" x t cd "(snd (allocate (Memory st)))" ] by fastforce
    then have a30: "\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow> accessStore locs (Memory st) = accessStore locs m"
      by (metis allocateSameAccess)
    have st'IsM:"Memory st' = m" using 4 by simp
    have tloc:"Toploc (Memory st) < Toploc (snd (allocate (Memory st)))" unfolding allocate_def by simp
    show "lessThanTopLocs (Memory st')" unfolding lessThanTopLocs_def
    proof intros
      fix tloc loc
      assume b10: "Toploc (Memory st') \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
      then have b20:"Toploc (Memory st) \<le> tloc" using a10 tloc st'IsM by simp
      have "\<not>LSubPrefL2 loc p'"
      proof(rule ccontr)
        assume c10:"\<not> \<not> LSubPrefL2 loc p'"
        then have c20: "LSubPrefL2 loc p'" by simp
        then have c30:"LSubPrefL2 p' (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)" using b10 MemLSubPrefTransitive by auto
        then show False
        proof -
          have "MCon t' (Memory st) p'" using 4(4) 2(1) unfolding TypeSafe_def typeCompat_def using lInDen by fastforce
          then obtain x i where c40: "accessStore p' (Memory st) = Some x \<or> accessStore (hash p' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some x" using MCon_imps_Some by blast
          then show ?thesis
          proof(cases "accessStore p' (Memory st) = Some x")
            case True
            then show ?thesis using lessThanSome_imps_Locs[of "(state.Memory st)" p' x tloc] c30 a15 b20 by simp
          next
            case False
            then have "accessStore (hash p' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some x" using c40 by simp
            then show ?thesis using lessThanSome_imps_Locs_hash c30 a15 b20 by fastforce
          qed
        qed
      qed
      then show "accessStore loc (Memory st') = None " using b10 b20 a20 a10 st'IsM a15 a30
        by (metis (no_types, lifting) LSubPrefL2_def MemLSubPrefTransitive antisym_conv2 hash_inequality hash_suffixes_associative hashesIntSame lessThanTopLocs_def order_less_le_trans tloc)

    next
      fix loc y
      assume "accessStore loc (Memory st') = Some y "
      then show "\<exists>tloc<Toploc (Memory st'). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
        by (metis a10 a15 a30 lessThanTopLocs_def order_less_trans st'IsM tloc)
    qed
  next
    show ns:"typeCompat (Denvalue env) (Stack st') (Memory st') (Storage st' (Address env)) cd"
      unfolding typeCompat_def
    proof intros
      fix t'' l'
      assume inDen:" (t'', l') |\<in>| fmran (Denvalue env)"
      show " denvalueCon (Stack st') (Memory st') (Storage st' (Address env)) cd t'' l'"
      proof(cases l')
        case (Stackloc x1)
        then obtain a where adef:"accessStore x1 (Stack st') = Some a" using inDen Stackloc 2(1) unfolding TypeSafe_def typeCompat_def using accessLStack nonChangedStack by fastforce
        then show ?thesis
        proof(cases "a")
          case (KValue x1)
          then show ?thesis using Stackloc adef inDen Stackloc 2(1) accessLStack nonChangedStack unfolding TypeSafe_def typeCompat_def
            by (metis (no_types, lifting) denvalue.simps(5) Option.option.simps(5) stackvalue.distinct(3) stackvalue.simps(17) option.inject)
        next
          case (KCDptr x2)
          then show ?thesis using Stackloc adef inDen Stackloc 2(1) accessLStack nonChangedStack unfolding TypeSafe_def typeCompat_def
            by (metis (no_types, lifting) denvalue.simps(5) Option.option.simps(5) stackvalue.distinct(7) stackvalue.simps(18) option.inject)
        next
          case (KMemptr x3)
          then have "\<exists>struct. t'' = type.Memory struct"
          proof(cases "x1 = l")
            case True
            have "accessStore l (Stack st) = Some (KMemptr p')" using 4(4) by simp
            then show ?thesis using Stackloc adef inDen Stackloc 2(1) KMemptr True unfolding TypeSafe_def typeCompat_def by (cases t'';force+)
          next
            case False
            then have "accessStore x1 (Stack st) = accessStore x1 (Stack st')" using accessLStack nonChangedStack by simp
            then show ?thesis using Stackloc adef inDen Stackloc 2(1) KMemptr unfolding TypeSafe_def typeCompat_def by (cases t'';force+)
          qed
          then obtain struct where structdef:"t'' = type.Memory struct" by blast


          have "MCon struct (Memory st') x3"
          proof(cases "x1 = l")
            case True
            then have "x3 = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" using 4 KMemptr adef unfolding accessStore_def updateStore_def by auto
            moreover have "(MTArray x t) = struct"
              by (metis 2(1) "4"(3) Stackloc True type.inject(3) fst_conv inDen lInDen snd_conv TypeSafe_def
                  structdef unique_locations_def)
            ultimately show ?thesis using MCondest 4 Stackloc True inDen lInDen mInStd structdef by metis
          next
            case False
            then have "accessStore x1 (Stack st) = accessStore x1 (Stack st')" using accessLStack nonChangedStack by simp
            then have "accessStore x1 (Stack st) = Some (KMemptr x3)" using adef KMemptr by simp
            then have mgh:"MCon struct (Memory st) x3" using inDen KMemptr Stackloc adef structdef 2(1) unfolding TypeSafe_def typeCompat_def by force
            then show ?thesis using originalMConStillMCon[OF mgh limitSt ] mInStd allocateSameAccess a30 by (metis nonLocChanged)

          qed

          then show ?thesis using structdef KMemptr Stackloc adef inDen Stackloc 2(1) unfolding TypeSafe_def by simp

        next
          case (KStoptr x4)
          then show ?thesis using Stackloc adef sameStorage inDen Stackloc KStoptr 2(1) accessLStack nonChangedStack unfolding TypeSafe_def typeCompat_def
            apply(cases t'')
               apply (metis (no_types, lifting) denvalue.simps(5) Option.option.simps(5) stackvalue.simps(20) type.distinct(3) type.simps(17) lInDen old.prod.inject snd_eqD uniqueLocs)
              apply (metis (no_types, lifting) denvalue.simps(5) Option.option.simps(5) stackvalue.simps(20) type.distinct(7) type.simps(18) lInDen old.prod.inject snd_eqD uniqueLocs)

             apply (metis (no_types, lifting) denvalue.simps(5) Option.option.simps(5) stackvalue.distinct(11) stackvalue.simps(20) type.simps(19) option.inject)

            by (metis (no_types, lifting) denvalue.simps(5) Option.option.simps(5) stackvalue.simps(20) type.distinct(11) type.simps(20) lInDen prod.inject snd_conv uniqueLocs)
        qed

        next
        case (Storeloc x2)
        then show ?thesis using sameStorage inDen 2(1) unfolding TypeSafe_def typeCompat_def by (cases t''; force)
      qed
    qed

    next
    have accSame:"Accounts st'= Accounts st" using 4 by auto
    from 2(3)
    obtain c_fi ct_fi dud_fi where fi:"
         Type (Accounts st (Address env)) = Some (atype.Contract c_fi) \<and>
         Contract env = c_fi \<and>
         ep $$ c_fi = Some (ct_fi, dud_fi) \<and>
         (\<forall>id v. (ct_fi $$ id = Some (Var v)) = (Denvalue env $$ id = Some (type.Storage v, Storeloc id))) \<and>
         (\<forall>id v loc. Denvalue env $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc) \<and>
         (\<forall>t'' l'' p''.
             (type.Storage t'', Stackloc l'') |\<in>| fmran (Denvalue env) \<and> accessStore l'' (Stack st) = Some (KStoptr p'') \<longrightarrow>
             (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue env) \<and> CompStoType t' t'' l' p''))"
        unfolding fullyInitialised_def by blast
    have fiPtrs':"\<forall>t'' l'' p''.
             (type.Storage t'', Stackloc l'') |\<in>| fmran (Denvalue env) \<and> accessStore l'' (Stack st') = Some (KStoptr p'') \<longrightarrow>
             (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue env) \<and> CompStoType t' t'' l' p'')"
    proof (intro allI impI)
      fix t'' l'' p''
      assume in1:"(type.Storage t'', Stackloc l'') |\<in>| fmran (Denvalue env)\<and>accessStore l'' (Stack st') = Some (KStoptr p'')"
      then show "\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue env) \<and> CompStoType t' t'' l' p''"
          using 4 fi unfolding accessStore_def updateStore_def
          by (metis 2(1) type.distinct(11) accessStore_def lInDen nonChangedStack prod.inject snd_eqD typeSafeUnique uniqueLocs)
    qed
    show "fullyInitialised env (Accounts st') (Stack st')"
        unfolding fullyInitialised_def using fi fiPtrs' accSame by metis

    next
    have a20':"\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow> accessStore locs (snd (allocate (Memory st))) = accessStore locs m"
        using 4(6) unfolding cpm2m_def using cpm2mSingleChange[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd "(snd (allocate (Memory st)))" x m ]
          cpm2m_def[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" x t cd "(snd (allocate (Memory st)))" ] by fastforce
    then have a30': "\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow> accessStore locs (Memory st) = accessStore locs m"
        by (metis allocateSameAccess)
    have tloc:"Toploc (Memory st) < Toploc (snd (allocate (Memory st)))" unfolding allocate_def by simp
    have topLocEq:"Toploc (snd (allocate (Memory st))) = Toploc (Memory st')"
        using cpm2mTopLocSame 4(6) cpm2m_def mInStd MCondest
        by (metis (no_types, lifting) MCon.simps(2))
    next
    show "denvalueTypeCorrectness env (Stack st') (Memory st')"
        unfolding denvalueTypeCorrectness_def
    proof(intros)
      fix t2 l2 ptr_loc sub_loc
      assume *:"(type.Memory t2, Stackloc l2) |\<in>| fmran (Denvalue env) \<and> accessStore l2 (Stack st') = Some (KMemptr ptr_loc)"

      show "case t2 of MTArray len arr \<Rightarrow> (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr)

     | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st') = Some (MTValue val)"
      proof(cases "ptr_loc = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))")
        case False
        then have sameACC:"accessStore l2 (Stack st') = accessStore l2 (Stack st)"
            using nonChangedStack * 4(5) unfolding accessStore_def updateStore_def
            by (metis stackvalue.inject(3) accessLStack accessStore_def option.inject)
        then have mcOld:"MCon t2 (Memory st) ptr_loc" using * by (metis 2(1) sameMemTSafe)
        then have old:"(case t2 of MTArray len arr \<Rightarrow>
(\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr)
       | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st) = Some (MTValue val))"
            using sameACC 2(1) * unfolding TypeSafe_def denvalueTypeCorrectness_def by fastforce

        have inDenvalue:"(type.Memory t2, Stackloc l2) |\<in>| fmran (Denvalue env)" using * by simp
        have lims:"\<not> LSubPrefL2 ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> \<not> LSubPrefL2 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) ptr_loc"
            using typeSafe_noDenElementOverToploc_mem[OF 2(1) inDenvalue] * sameACC
            using LSubPrefL2_def MemLSubPrefTransitive by metis

        then show ?thesis
        proof(cases t2)
          case (MTArray x11 x12)
          have nonLocChanged_TypedSafe:"\<forall>loc. \<not> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))
                                        \<longrightarrow> accessTypeStore loc (Memory st') = accessTypeStore loc (Memory st)"
              using lims mInStd 4(6) unfolding cpm2m_def
              by (metis allocateTypeSameAccess cpm2mSingleChange_Typed cpm2m_def)
          have nonLocChanged_TypedSafe2:"\<forall>loc. \<not> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))
                                        \<longrightarrow> accessStore loc (Memory st') = accessStore loc (Memory st)"
              using lims mInStd 4(6) cpm2mSingleChange unfolding cpm2m_def
              by (metis allocateSameAccess cpm2m_def)
          have "\<forall>i. \<not> LSubPrefL2 (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))"
              using lims Mutual_NonSub_SpecificNonSub by blast
          then show ?thesis using old MTArray nonLocChanged_TypedSafe nonLocChanged_TypedSafe2 lims by simp
          next
          case (MTValue x2)
          have "\<not> LSubPrefL2 ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" using lims by simp
          then have "accessTypeStore ptr_loc (Memory st') = accessTypeStore ptr_loc (Memory st)"
              by (metis "4"(6) allocateTypeSameAccess cpm2mSingleChange_Typed cpm2m_def mInStd)
          then show ?thesis using MTValue old by simp
        qed
        next
        case True
        then have newLocation:"l2 = l \<and> t2 = (MTArray x t)"
            using lInDen accessLStack *
            by (metis 2(1) "4"(3) LSubPrefL2_def Pair_inject type.inject(3) nonChangedStack snd_eqD typeSafeUnique typeSafe_noDenElementOverToploc_mem
                unique_locations_def)
        then have l2IsL:"l2 = l" using newLocation by simp
        then have conc0:"ptr_loc = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" using * 4(5,7) by auto
        have conc1:"\<forall>i<x. accessTypeStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some t"
            using 4(6) unfolding cpm2m_def
            using cpm2m_TypeCompChangeIndexs[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd "(snd (allocate (Memory st)))" x m]
              mInStd by simp
        have nonLocChanged_TypedSafe2:"\<forall>loc. \<not> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<or> loc = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))
                                        \<longrightarrow> accessStore loc (Memory st') = accessStore loc (Memory st)"
            using mInStd 4(6) unfolding cpm2m_def
            by (metis allocateSameAccess cpm2mSingleChange cpm2m_def)
        then show ?thesis using conc1 conc0 newLocation
            using LSubPrefL2_def limitSt by fastforce

      qed
    qed
    next
    have old:"subPrefixStructuralConsistency (Memory st)"
        using 2(1) unfolding TypeSafe_def by simp
    have none:"accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (Memory st) = None"
        by (simp add: \<open>accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (snd (allocate (Memory st))) = None\<close> allocateSame)
    have lessT:"lessThanTopLocs (Memory st)" using 2(1) unfolding TypeSafe_def by simp
    have someV:"SomeValSomeTyp (Memory st)"
        using 2(1) unfolding TypeSafe_def by simp
    have nonCha:"\<forall>locs. \<not> TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x t) \<longrightarrow>
           accessStore locs (Memory st) = accessStore locs (Memory st')"
        using a30 allocateSame mInStd by presburger
    have index:"\<forall>i<x. accessTypeStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some t"
        using "4"(6) cpm2m_TypeCompChangeIndexs cpm2m_def mInStd by auto
    have subs:"\<forall>destl'.
   TypedMemSubPref destl' (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x t) \<longrightarrow>
   (\<exists>stt. CompMemType (Memory st') x t stt (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) destl' \<and>
          (case stt of
           MTArray parent_len parent_arr \<Rightarrow>
             \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some parent_arr
           | MTValue pval \<Rightarrow> accessTypeStore destl' (Memory st') = Some (MTValue pval)))"
        using cpm2m_TypeCompChange "4"(6) cpm2m_def mInStd by simp
    have subT:"\<forall>locs.
     \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<or> locs = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow>
     accessTypeStore locs (Memory st) = accessTypeStore locs (Memory st')"
        using "4"(6) mInStd unfolding cpm2m_def using cpm2mSingleChange_Typed[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd " (snd (allocate (Memory st)))" x m]
          allocateTypeSameAccess by metis
    have subT2:"\<forall>locs.
     \<not> TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x t) \<or> locs = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow>
     accessTypeStore locs (Memory st) = accessTypeStore locs (Memory st')"
        using "4"(6) mInStd unfolding cpm2m_def using cpm2mSingleChange_typedPref_typed[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd " (snd (allocate (Memory st)))" x m]
          allocateTypeSameAccess by metis
    show "subPrefixStructuralConsistency (Memory st')"
        using cpm2m_subPrefixPersist[OF old none someV subT lessT subT2 subs _ _ index _ nonCha] MCondest mInStd selfPoint nonLocChanged
        by (metis (no_types, lifting) "4"(6) allocateSame cpm2mSingleChange cpm2m_def)
    next
    have old:"(\<forall>locs. (\<exists>t. accessStore locs (Memory st) = Some t) = (\<exists>tt. accessTypeStore locs (Memory st) = Some tt))"
        using 2(1) unfolding TypeSafe_def SomeValSomeTyp_def by blast
    have somesome:"\<forall>destl'. TypedMemSubPref destl' (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x t)
        \<longrightarrow> (\<exists>t. accessStore destl' m = Some t) = (\<exists>tt. accessTypeStore destl' m = Some tt)"
        using 4(6) unfolding cpm2m_def using cpm2m_TypeCompChange_somesome[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd "(snd (allocate (Memory st)))" x m]
        by simp
    have a30T:"\<forall>locs. \<not> TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x t)
        \<longrightarrow> accessTypeStore locs (Memory st) = accessTypeStore locs (Memory st')"
        using 4(6) unfolding cpm2m_def using cpm2mSingleChange_typedPref_typed[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd " (snd (allocate (Memory st)))" x m ]
          mInStd allocateTypeSameAccess by metis
    show "SomeValSomeTyp (Memory st')"unfolding SomeValSomeTyp_def
    proof intros
      fix locs
      show "(\<exists>t. accessStore locs (Memory st') = Some t) = (\<exists>tt. accessTypeStore locs (Memory st') = Some tt) "
      proof(cases "TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x t)")
        case True
        then have "(\<exists>t. accessStore locs m = Some t) = (\<exists>tt. accessTypeStore locs m = Some tt)"
            using somesome by simp
        then show ?thesis using mInStd by simp
        next
        case False
        then have "accessStore locs (Memory st) = accessStore locs (Memory st')"
            using a30 mInStd allocateSameAccess by metis
        moreover have "accessTypeStore locs (Memory st) = accessTypeStore locs (Memory st')"
            using a30T False by simp
        ultimately show ?thesis using old by metis
      qed
    qed
    fix locs t'
    assume in1:"accessTypeStore locs (Memory st) = Some t'"
    show "accessTypeStore locs (Memory st') = Some t'"
    proof(cases "TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x t)")
      case True
      then show ?thesis using 2(1) in1 unfolding TypeSafe_def lessThanTopLocs_def
          by (metis Suc_n_not_le_n neg_MemLSubPrefL2_imps_TypedMemSubPref not_less_eq_eq old option.distinct(1))
      next
      case False
      then show ?thesis using in1 4(6) unfolding cpm2m_def using cpm2mSingleChange_typedPref_typed[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd " (snd (allocate (Memory st)))" x m ]
            mInStd allocateTypeSameAccess by metis
    qed
    next
    show "\<And>locs v. accessStore locs (Memory st) = Some (MPointer v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MPointer v')"
      using allocateSame limitSt mInStd nonLocChanged by (metis dual_order.refl option.discI)
    next
    show "\<And>locs v. accessStore locs (Memory st) = Some (MValue v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MValue v')"
        by (metis allocateSameAccess limitSt mInStd nonLocChanged option.distinct(1) order_eq_refl)
    next
    show " \<And>i loc. i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<Longrightarrow> accessStore loc
        (Memory st) = None \<Longrightarrow> accessStore loc (Memory st') = None"

        by (metis LSubPrefL2_def MemLSubPrefTransitive Read_Show_nat'_id allocateSame hash_flatten_right hash_inequality mInStd nat_less_le nonLocChanged)
    next
    have tloc:"Toploc (Memory st) < Toploc (snd (allocate (Memory st)))" unfolding allocate_def by simp
    have topLocEq:"Toploc (snd (allocate (Memory st))) = Toploc (Memory st')"
        using cpm2mTopLocSame 4(6) cpm2m_def mInStd MCondest
        by (metis (no_types, lifting) MCon.simps(2))
    then show "Toploc (Memory st) \<le> Toploc (Memory st')" using tloc by simp
  qed
qed

text \<open>Assignment case 5: a calldata array assigned to a storage variable reached through a stack pointer: the array is copied into storage.\<close>

lemma TypeSafe_Assign_5:
  assumes "TypeSafe env (Accounts st) (Stack st) (Memory st) (Storage st) cd"
    and "stmt (ASSIGN lv ex) env cd st = Normal ((), st')"
    and "fullyInitialised env (Accounts st) (Stack st)"
    and "expr ex env cd (st\<lparr>state.Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>) (state.Gas st - costs (ASSIGN lv
        ex) env cd st) = Normal ((KCDptr p, Calldata (MTArray x t)), g)"
    and "lexp lv env cd (st\<lparr>state.Gas := g\<rparr>) g = Normal((LStackloc l, type.Storage t'),g')"
    and "accessStore l (Stack st) = Some (KStoptr p')"
    and "cps2mTypeCompatible t' (MTArray x t) "
    and "cpm2s p p' x t cd (Storage st (Address env)) = Some s"
    and "st' = st\<lparr>state.Gas := g', Storage := (Storage st) (Address env := s)\<rparr>"
  shows "StateInvariant env st st' cd"
proof -
  let ?case = "StateInvariant env st st' cd"
  note 2 = assms(1-3)
  note 5 = assms(4-9)
  obtain t''' where t''Def:"t' = STArray x t''' " using 5(4)
    by (metis stypes.exhaust cps2mTypeCompatible.simps(2,4,6))
  have sameStack:"(Stack st) = (Stack st')" using 5 unfolding accessStore_def updateStore_def by auto
  have sameMemory:"Memory st' = Memory st " using 5 by auto
  have lInDen:"(type.Storage t', Stackloc l) |\<in>| fmran (Denvalue env)"
    using lexpStackloc_imps_inDen[of lv env cd ] 5(2) by simp
  have nonLocChanged:"\<forall>t' locs. \<not> LSubPrefL2 locs p' \<or> locs = p' \<longrightarrow> accessStorage t' locs (Storage st (Address env)) = accessStorage t' locs s"
    using 5(5) unfolding cpm2s_def using cpm2sSingleChange[of p p' t cd "(Storage st (Address env))" x s]
    by fastforce
  have a30:" \<forall>locs t' t''.
     cps2mTypeCompatible (STArray x t') (MTArray x t) \<and> locs \<noteq> p' \<and> \<not> TypedStoSubpref locs p' (STArray x t') \<longrightarrow>
     accessStorage t'' locs (Storage st (Address env)) = accessStorage t'' locs s"
    using 5(5) unfolding cpm2s_def using cpm2sSingleChange_typedPref[of p "p'" t cd "(Storage st (Address env))" x s ] by simp
  then have a35:"\<forall>locs t''. locs \<noteq> p' \<and> \<not> TypedStoSubpref locs p' (STArray x t''') \<longrightarrow>
     accessStorage t'' locs (Storage st (Address env)) = accessStorage t'' locs (Storage st' (Address env))"
    using 5 t''Def by auto
  have mInStd:"s = Storage st' (Address env)" using 5 by simp

  have p'MCon:"SCon t' p' (Storage st (Address env))" using 2 5 unfolding TypeSafe_def typeCompat_def using lInDen
    by (auto split:denvalue.splits option.splits stackvalue.splits type.splits)

  have MConsrc:"MCon (MTArray x t) cd (extractValueType (KCDptr p)) \<and> (\<exists>xx. KCDptr p = KCDptr xx) \<and>
          (\<exists>stloc tp'' pa.
          (Calldata tp'', Stackloc stloc) |\<in>| fmran (Denvalue env) \<and>
          accessStore stloc (Stack (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)) = Some (KCDptr pa) \<and>
          (tp'' = (MTArray x t) \<and> KCDptr p = KCDptr pa \<or>
           (\<exists>len arr. extractValueType (KCDptr p) \<noteq> pa \<and> tp'' = MTArray len arr \<and> CompMemType cd len arr (MTArray x t) pa (extractValueType (KCDptr p)))))"
    using 2(1) 5(1) exprTypeconInduct(3)[of ex env cd "(st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)"
        "(state.Gas st - costs (ASSIGN lv ex) env cd st)" "KCDptr p" "Calldata (MTArray x t)" g]
      2(3) unfolding fullyInitialised_def
    by (auto split:type.splits if_splits )

  note limitSt1 = TypeSafe_memory_bounds(1)[OF 2(1)]
  note limitSt = TypeSafe_memory_bounds(2)[OF 2(1)]
  moreover have allocateSame:"\<forall>loc. accessStore loc (Memory st) = accessStore loc (snd (allocate (Memory st)))" using allocateSameAccess by blast
  ultimately have "accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (snd (allocate (Memory st))) = None" using LSubPrefL2_def by auto
  then have SCondest:"SCon (STArray x t''') p' s" using 5 unfolding cpm2s_def
    using MCon_cpm2s[of p p' t cd "(Storage st (Address env))" x s t'''] t''Def MConsrc extractValueType.simps(2) by metis
  then have SCondest2:"SCon (STArray x t''') p' (Storage st' (Address env))"
    by (simp add: mInStd)
  then have SCondest3:"SCon t' p' (Storage st' (Address env))"
    by (simp add: mInStd t''Def)

  have stackDenvalLimits:"\<forall>struct loc stloc. (type.Memory struct, Stackloc loc) |\<in>| fmran (Denvalue env)
                          \<and> accessStore loc (Stack st) = Some (KMemptr stloc) \<longrightarrow> \<not> LSubPrefL2 stloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))"
    using typeSafe_noDenElementOverToploc_mem[OF 2(1)] by auto

  show ?thesis unfolding TypeSafe_def StateInvariant_def
  proof intros
    show "AddressTypes (Accounts st')" using 2(1) 5 unfolding TypeSafe_def by simp
  next
    show "unique_locations (Denvalue env)" using 2(1) unfolding TypeSafe_def by simp
  next
    have a0:" compPointers (Stack st) (Denvalue env)" using 2(1) unfolding TypeSafe_def by blast
    show "compPointers (Stack st') (Denvalue env)" unfolding compPointers_def
    proof(intros)
      fix tp1 tp2 l1 l2 l1' l2' stl1 stl2
      assume a1:"(type.Storage tp1, l1) |\<in>| fmran (Denvalue env) \<and>
     (type.Storage tp2, l2) |\<in>| fmran (Denvalue env) \<and>
     (l1 = Stackloc l1' \<and> accessStore l1' (Stack st') = Some (KStoptr stl1) \<or> l1 = Storeloc stl1) \<and> (l2 = Stackloc l2'
         \<and> accessStore l2' (Stack st') = Some (KStoptr stl2) \<or> l2 = Storeloc stl2)"
      then show " if TypedStoSubpref stl2 stl1 tp1 then CompStoType tp1 tp2 stl1 stl2 else if TypedStoSubpref stl1 stl2 tp2 then CompStoType tp2 tp1 stl2 stl1 else True"
      proof(cases "TypedStoSubpref stl2 stl1 tp1")
        case True
        then show ?thesis using a1 sameStack a0 unfolding compPointers_def by simp
      next
        case f1:False
        then show ?thesis
        proof(cases "TypedStoSubpref stl1 stl2 tp2")
          case True
          then show ?thesis using a1 sameStack a0 unfolding compPointers_def by simp
        next
          case False
          then show ?thesis using f1 by simp
        qed
      qed
    qed
  next
    have scOld:"safeContract (Accounts st) (Storage st)" using 2(1) unfolding TypeSafe_def by simp
    show "safeContract (Accounts st') (Storage st')" unfolding safeContract_def
    proof intros
      fix e ct dud i tp
      assume *:"Type (Accounts st' (Address (e::environment))) = Some (atype.Contract (Contract e)) \<and>
               ep $$ Contract (e::environment) = Some (ct, dud) \<and>
               ct $$ i = Some (Var tp)"
      show "SCon tp i (Storage st' (Address e))"
      proof (cases "Address e = Address env")
        case False
        then have sameAddr:"Storage st' (Address e) = Storage st (Address e)" using 5 by simp
        moreover have "SCon tp i (Storage st (Address e))"
          using * scOld 5 unfolding safeContract_def
          by fastforce
        ultimately show ?thesis by simp
      next
        case addrEq:True
        have typedOld:"Type (Accounts st (Address e)) = Some (atype.Contract (Contract e))"
          using * 5 by simp
        have epOld:"ep $$ Contract e = Some (ct, dud)"
          using * by simp
        have ctOld:"ct $$ i = Some (Var tp)"
          using * by simp
        have denI:"Denvalue env $$ i = Some (type.Storage tp, Storeloc i)"
          using fi_contract_var_to_denvalue_storeloc[OF 2(3) addrEq typedOld epOld ctOld] .
        have inDenI:"(type.Storage tp, Storeloc i) |\<in>| fmran (Denvalue env)"
          using denI by (simp add: fmranI)
        have oldSConE:"SCon tp i (Storage st (Address e))"
          using scOld typedOld epOld ctOld unfolding safeContract_def by blast
        have oldSCon:"SCon tp i (Storage st (Address env))"
          using oldSConE addrEq by simp
        have cmpPtr:"(if TypedStoSubpref p' i tp then CompStoType tp t' i p'
                       else if TypedStoSubpref i p' t' then CompStoType t' tp p' i else True)"
          using 2(1) 5(3) inDenI lInDen t''Def unfolding TypeSafe_def compPointers_def by blast
        have newSCon:"SCon tp i (Storage st' (Address env))"
          using SCon_update_array_subloc_cases[OF cmpPtr SCondest2 SCondest3 oldSCon t''Def a35] .
        show ?thesis using newSCon addrEq by simp
      qed
    qed
  next
    show "balanceTypes (Accounts st')" using 5 using 2(1) unfolding TypeSafe_def by simp
  next
    have "envAddressesWellFormed env" using 2(1) unfolding TypeSafe_def by simp
    then show "addressFormat (Address env)" and "addressFormat (Sender env)" by simp+
  next
    show "svalueTypes (Svalue env)" using 2(1) unfolding TypeSafe_def by simp
  next
    have *:"((\<forall>tloc loc. Toploc (Stack st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Stack st) = None) \<and>
            (\<forall>loc y. accessStore loc (Stack st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Stack st). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))) "
      using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by simp
    have **:"Toploc (Stack st) = Toploc (Stack st')" using 5 unfolding updateStore_def by auto
    show "lessThanTopLocs (Stack st')" using sameStack * ** unfolding lessThanTopLocs_def by auto
  next
    show "lessThanTopLocs cd" using 2(1) unfolding TypeSafe_def by simp
  next
    show "lessThanTopLocs (Memory st')" using sameMemory unfolding lessThanTopLocs_def
      by (simp add: limitSt limitSt1)
  next
    show tcN:"typeCompat (Denvalue env) (Stack st') (Memory st') (Storage st' (Address env)) cd"
      unfolding typeCompat_def
    proof intros
      fix t'' l'
      assume inDen:" (t'', l') |\<in>| fmran (Denvalue env)"

      show "denvalueCon (Stack st') (Memory st') (Storage st' (Address env)) cd t'' l'"
      proof(cases l')
        case (Stackloc x1)
        then obtain a where adef:"accessStore x1 (Stack st') = Some a" using inDen Stackloc 2(1) unfolding TypeSafe_def typeCompat_def using sameStack by fastforce
        then show ?thesis
        proof(cases "a")
          case (KValue x1)
          then show ?thesis using Stackloc adef inDen Stackloc 2(1) sameStack unfolding TypeSafe_def typeCompat_def
            by (metis (no_types, lifting) denvalue.simps(5) Option.option.simps(5) stackvalue.simps(17) )
        next
          case (KCDptr x2)
          then show ?thesis using Stackloc adef inDen Stackloc 2(1) sameStack unfolding TypeSafe_def typeCompat_def
            by (metis (no_types, lifting) denvalue.simps(5) Option.option.simps(5) stackvalue.simps(18))
        next
          case (KMemptr x3)
          then show ?thesis using Stackloc adef inDen Stackloc 2(1) sameStack sameMemory unfolding TypeSafe_def typeCompat_def by (cases t''; fastforce)
        next
          case (KStoptr x4)
          then obtain struct where structDef: "t'' = type.Storage struct" using Stackloc adef inDen Stackloc 2(1) sameStack unfolding TypeSafe_def typeCompat_def
            by (cases t''; fastforce)

          have cmpStoPtr:"(
            (type.Storage struct, l') |\<in>| fmran (Denvalue env) \<and>
            (type.Storage (STArray x t'''), Stackloc l) |\<in>| fmran (Denvalue env) \<and>
            (l' = Stackloc x1 \<and> accessStore x1 (Stack st) = Some (KStoptr x4) \<or> l' = Storeloc x4) \<and>
            (accessStore l (Stack st) = Some (KStoptr p')) \<longrightarrow>
            (if TypedStoSubpref p' x4 struct then CompStoType struct (STArray x t''') x4 p'
             else if TypedStoSubpref x4 p' (STArray x t''') then CompStoType (STArray x t''') struct p' x4 else True))"
            using 2(1) 5(3) lInDen inDen Stackloc structDef KStoptr unfolding TypeSafe_def compPointers_def by blast

          then have cmpStoPtr2:"(if TypedStoSubpref p' x4 struct then CompStoType struct (STArray x t''') x4 p'
           else if TypedStoSubpref x4 p' (STArray x t''') then CompStoType (STArray x t''') struct p' x4 else True)"
            using 5(3) lInDen inDen Stackloc structDef KStoptr t''Def
            by (simp add: adef sameStack)

          have SConx4Old:"SCon struct x4 (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using Stackloc adef inDen Stackloc 2(1) sameStack structDef KStoptr
            by fastforce

          have cmpStoPtr3:"(if TypedStoSubpref p' x4 struct then CompStoType struct t' x4 p'
            else if TypedStoSubpref x4 p' t' then CompStoType t' struct p' x4 else True)"
            using cmpStoPtr2 t''Def by blast
          have "SCon struct x4 (Storage st' (Address env))"
            using SCon_update_array_subloc_cases[OF cmpStoPtr3 SCondest2 SCondest3 SConx4Old t''Def a35] .
          then show ?thesis using Stackloc adef inDen Stackloc 2(1) sameStack KStoptr structDef by simp
        qed

      next
        case (Storeloc x2)
        then obtain struct where structDef: "t'' = type.Storage struct" using Storeloc inDen 2(1) sameStack unfolding TypeSafe_def typeCompat_def
          by (cases t''; fastforce)

        have cmpStoPtr:"(
            (type.Storage struct, l') |\<in>| fmran (Denvalue env) \<and>
            (type.Storage (STArray x t'''), Stackloc l) |\<in>| fmran (Denvalue env) \<and>
             l' = Storeloc x2) \<and>
            (accessStore l (Stack st) = Some (KStoptr p')) \<longrightarrow>
            (if TypedStoSubpref p' x2 struct then CompStoType struct (STArray x t''') x2 p'
             else if TypedStoSubpref x2 p' (STArray x t''') then CompStoType (STArray x t''') struct p' x2 else True)"
          using 2(1) 5(3) lInDen inDen Storeloc structDef unfolding TypeSafe_def compPointers_def by blast

        then have cmpStoPtr2:"(if TypedStoSubpref p' x2 struct then CompStoType struct (STArray x t''') x2 p'
             else if TypedStoSubpref x2 p' (STArray x t''') then CompStoType (STArray x t''') struct p' x2 else True)"
          using 5(3) lInDen inDen Storeloc structDef t''Def by (simp add: sameStack)

        have SConx4Old:"SCon struct x2 (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using Storeloc inDen 2(1) sameStack structDef
          by fastforce

        have cmpStoPtr3:"(if TypedStoSubpref p' x2 struct then CompStoType struct t' x2 p'
          else if TypedStoSubpref x2 p' t' then CompStoType t' struct p' x2 else True)"
          using cmpStoPtr2 t''Def by fastforce
        have "SCon struct x2 (Storage st' (Address env))"
          using SCon_update_array_subloc_cases[OF cmpStoPtr3 SCondest2 SCondest3 SConx4Old t''Def a35] .
        then show ?thesis using Storeloc inDen 2(1) sameStack Storeloc structDef by simp
      qed
    qed
    then have "typeCompat (Denvalue env) (Stack st) (Memory st') (Storage st' (Address env)) cd"
      using sameStack by auto

  next

    have accSame:"Accounts st'= Accounts st" using 5 by auto
    from 2(3)
    obtain c_fi ct_fi dud_fi where fi:"
         Type (Accounts st (Address env)) = Some (atype.Contract c_fi) \<and>
         Contract env = c_fi \<and>
         ep $$ c_fi = Some (ct_fi, dud_fi) \<and>
         (\<forall>id v. (ct_fi $$ id = Some (Var v)) = (Denvalue env $$ id = Some (type.Storage v, Storeloc id))) \<and>
         (\<forall>id v loc. Denvalue env $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc) \<and>
         (\<forall>t'' l'' p''.
             (type.Storage t'', Stackloc l'') |\<in>| fmran (Denvalue env) \<and> accessStore l'' (Stack st) = Some (KStoptr p'') \<longrightarrow>
             (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue env) \<and> CompStoType t' t'' l' p''))"
      unfolding fullyInitialised_def by blast
    have fiPtrs':"\<forall>t'' l'' p''.
             (type.Storage t'', Stackloc l'') |\<in>| fmran (Denvalue env) \<and> accessStore l'' (Stack st') = Some (KStoptr p'') \<longrightarrow>
             (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue env) \<and> CompStoType t' t'' l' p'')"
    proof (intro allI impI)
      fix t'' l'' p''
      assume in1:"(type.Storage t'', Stackloc l'') |\<in>| fmran (Denvalue env)\<and>accessStore l'' (Stack st') = Some (KStoptr p'')"
      then show "\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue env) \<and> CompStoType t' t'' l' p''"
        using 5 fi unfolding accessStore_def updateStore_def
        using 2(1) type.distinct(11) accessStore_def lInDen prod.inject snd_eqD typeSafeUnique uniqueLocs
        by simp
    qed
    show "fullyInitialised env (Accounts st') (Stack st')"
      unfolding fullyInitialised_def using fi fiPtrs' accSame by metis
  next
    have cc0:"\<forall>l ptr_loc. accessStore l (Stack st') = Some (KMemptr ptr_loc) \<longrightarrow> accessStore l (Stack st) = Some (KMemptr ptr_loc)"
      using 5(6) unfolding updateStore_def accessStore_def by auto
    have sameMem:"Memory st = Memory st'" using 5(6) by simp
    show "denvalueTypeCorrectness env (Stack st') (Memory st')"
      unfolding denvalueTypeCorrectness_def
    proof intros
      fix t l ptr_loc
      assume "(type.Memory t, Stackloc l) |\<in>| fmran (Denvalue env) \<and>
     accessStore l (Stack st') = Some (KMemptr ptr_loc)"
      then have "(case t of
       MTArray len arr \<Rightarrow> (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr)
       | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st) = Some (MTValue val))"
        using 2(1) unfolding TypeSafe_def denvalueTypeCorrectness_def using cc0 by blast
      then show "case t of
     MTArray len arr \<Rightarrow> (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr)
     | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st') = Some (MTValue val)"
        using sameMem by metis
    qed
  next
    have sameMem:"Memory st = Memory st'" using 5(6) by simp
    show "subPrefixStructuralConsistency (Memory st')"
      using 2(1) sameMem unfolding TypeSafe_def by simp
  next
    show "SomeValSomeTyp (Memory st')" using 2(1) unfolding TypeSafe_def using 5(6) by simp
  next
    show "\<And>locs t. accessTypeStore locs (Memory st) = Some t \<Longrightarrow> accessTypeStore locs (Memory st') = Some t "
      using 5(6) by auto
  next
    show "\<And>locs v. accessStore locs (Memory st) = Some (MPointer v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MPointer v')"
      using 5(6) by simp
  next
    show "\<And>locs v. accessStore locs (Memory st) = Some (MValue v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MValue v')"
      using 5(6) by simp
  next
    show " \<And>i loc. i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<Longrightarrow> accessStore loc
        (Memory st) = None \<Longrightarrow> accessStore loc (Memory st') = None"
      using 5(6) by auto
  next
    show "Toploc (Memory st) \<le> Toploc (Memory st')" using 5(6) by simp
  qed
qed

text \<open>Assignment case 6: a calldata array assigned to a storage location: the array is copied into storage.\<close>

lemma TypeSafe_Assign_6:
  assumes "TypeSafe env (Accounts st) (Stack st) (Memory st) (Storage st) cd"
    and "stmt (ASSIGN lv ex) env cd st = Normal ((), st')"
    and "fullyInitialised env (Accounts st) (Stack st)"
    and "expr ex env cd (st\<lparr>state.Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>) (state.Gas st - costs (ASSIGN lv
        ex) env cd st) = Normal ((KCDptr p, Calldata (MTArray x t)), g)"
    and "lexp lv env cd (st\<lparr>state.Gas := g\<rparr>) g = Normal((LStoreloc l, type.Storage t'),g')"
    and "cps2mTypeCompatible t' (MTArray x t)"
    and "cpm2s p l x t cd (Storage st (Address env)) = Some s"
    and "st' = st\<lparr>state.Gas := g', Storage := (Storage st) (Address env := s)\<rparr>"
  shows "StateInvariant env st st' cd"
proof -
  let ?case = "StateInvariant env st st' cd"
  note 2 = assms(1-3)
  note 6 = assms(4-8)
  obtain t''' where t''Def:"t' = STArray x t''' " using 6(3)
    by (metis stypes.exhaust cps2mTypeCompatible.simps(2,4,6))
  have sameStack:"(Stack st) = (Stack st')" using 6 unfolding accessStore_def updateStore_def by auto
  have sameMemory:"Memory st' = Memory st " using 6 by auto
  have nonLocChanged:"\<forall>t' locs. \<not> LSubPrefL2 locs l \<or> locs = l \<longrightarrow> accessStorage t' locs (Storage st (Address env)) = accessStorage t' locs s"
    using 6(4) unfolding cpm2s_def using cpm2sSingleChange[of p l t cd "(Storage st (Address env))" x s]
    by fastforce
  have a30:" \<forall>locs t' t''.
     cps2mTypeCompatible (STArray x t') (MTArray x t) \<and> locs \<noteq> l \<and> \<not> TypedStoSubpref locs l (STArray x t') \<longrightarrow>
     accessStorage t'' locs (Storage st (Address env)) = accessStorage t'' locs s"
    using 6(4) unfolding cpm2s_def using cpm2sSingleChange_typedPref[of p "l" t cd "(Storage st (Address env))" x s ] by simp
  then have a35:"\<forall>locs t''. locs \<noteq> l \<and> \<not> TypedStoSubpref locs l (STArray x t''') \<longrightarrow>
     accessStorage t'' locs (Storage st (Address env)) = accessStorage t'' locs (Storage st' (Address env))"
    using 6 t''Def by auto
  have mInStd:"s = Storage st' (Address env)" using 6 by simp

  have MConsrc:"MCon (MTArray x t) cd (extractValueType (KCDptr p)) \<and> (\<exists>xx. KCDptr p = KCDptr xx) \<and>
          (\<exists>stloc tp'' pa.
          (Calldata tp'', Stackloc stloc) |\<in>| fmran (Denvalue env) \<and>
          accessStore stloc (Stack (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)) = Some (KCDptr pa) \<and>
          (tp'' = (MTArray x t) \<and> KCDptr p = KCDptr pa \<or>
           (\<exists>len arr. extractValueType (KCDptr p) \<noteq> pa \<and> tp'' = MTArray len arr \<and> CompMemType cd len arr (MTArray x t) pa (extractValueType (KCDptr p)))))"
    using 2(1) 6(1) exprTypeconInduct(3)[of ex env cd "(st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)"
        "(state.Gas st - costs (ASSIGN lv ex) env cd st)" "KCDptr p" "Calldata (MTArray x t)" g]
      2(3) unfolding fullyInitialised_def
    by (auto split:type.splits if_splits )

  note limitSt1 = TypeSafe_memory_bounds(1)[OF 2(1)]
  note limitSt = TypeSafe_memory_bounds(2)[OF 2(1)]
  moreover have allocateSame:"\<forall>loc. accessStore loc (Memory st) = accessStore loc (snd (allocate (Memory st)))" using allocateSameAccess by blast
  ultimately have "accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (snd (allocate (Memory st))) = None" using LSubPrefL2_def by auto
  then have SCondest:"SCon (STArray x t''') l s" using 6 unfolding cpm2s_def
    using MCon_cpm2s[of p l t cd "(Storage st (Address env))" x s t'''] t''Def MConsrc extractValueType.simps(2) by metis
  then have SCondest2:"SCon (STArray x t''') l (Storage st' (Address env))"
    by (simp add: mInStd)
  then have SCondest3:"SCon t' l (Storage st' (Address env))"
    by (simp add: mInStd t''Def)

  have stackDenvalLimits:"\<forall>struct loc stloc. (type.Memory struct, Stackloc loc) |\<in>| fmran (Denvalue env)
                          \<and> accessStore loc (Stack st) = Some (KMemptr stloc) \<longrightarrow> \<not> LSubPrefL2 stloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))"
    using typeSafe_noDenElementOverToploc_mem[OF 2(1)] by auto

  show ?thesis unfolding TypeSafe_def StateInvariant_def
  proof intros
    show "AddressTypes (Accounts st')" using 2(1) 6 unfolding TypeSafe_def by simp
  next
    show "unique_locations (Denvalue env)" using 2(1) unfolding TypeSafe_def by simp
  next
    have a0:" compPointers (Stack st) (Denvalue env)" using 2(1) unfolding TypeSafe_def by blast
    show "compPointers (Stack st') (Denvalue env)" unfolding compPointers_def
    proof(intros)
      fix tp1 tp2 l1 l2 l1' l2' stl1 stl2
      assume a1:"(type.Storage tp1, l1) |\<in>| fmran (Denvalue env) \<and>
     (type.Storage tp2, l2) |\<in>| fmran (Denvalue env) \<and>
     (l1 = Stackloc l1' \<and> accessStore l1' (Stack st') = Some (KStoptr stl1) \<or> l1 = Storeloc stl1) \<and> (l2 = Stackloc l2'
         \<and> accessStore l2' (Stack st') = Some (KStoptr stl2) \<or> l2 = Storeloc stl2)"
      then show " if TypedStoSubpref stl2 stl1 tp1 then CompStoType tp1 tp2 stl1 stl2 else if TypedStoSubpref stl1 stl2 tp2 then CompStoType tp2 tp1 stl2 stl1 else True"
      proof(cases "TypedStoSubpref stl2 stl1 tp1")
        case True
        then show ?thesis using a1 sameStack a0 unfolding compPointers_def by simp
      next
        case f1:False
        then show ?thesis
        proof(cases "TypedStoSubpref stl1 stl2 tp2")
          case True
          then show ?thesis using a1 sameStack a0 unfolding compPointers_def by simp
        next
          case False
          then show ?thesis using f1 by simp
        qed
      qed
    qed
  next
    have scOld:"safeContract (Accounts st) (Storage st)" using 2(1) unfolding TypeSafe_def by simp
    show "safeContract (Accounts st') (Storage st')" unfolding safeContract_def
    proof intros
      fix e ct dud i tp
      assume *:"Type (Accounts st' (Address (e::environment))) = Some (atype.Contract (Contract e)) \<and>
               ep $$ Contract (e::environment) = Some (ct, dud) \<and>
               ct $$ i = Some (Var tp)"
      show "SCon tp i (Storage st' (Address e))"
      proof (cases "Address e = Address env")
        case False
        then have sameAddr:"Storage st' (Address e) = Storage st (Address e)" using 6 by simp
        moreover have "SCon tp i (Storage st (Address e))"
          using * scOld 6 unfolding safeContract_def by fastforce
        ultimately show ?thesis by simp
      next
        case addrEq:True
        have typedOld:"Type (Accounts st (Address e)) = Some (atype.Contract (Contract e))"
          using * 6 by simp
        have epOld:"ep $$ Contract e = Some (ct, dud)"
          using * by simp
        have ctOld:"ct $$ i = Some (Var tp)"
          using * by simp
        have denI:"Denvalue env $$ i = Some (type.Storage tp, Storeloc i)"
          using fi_contract_var_to_denvalue_storeloc[OF 2(3) addrEq typedOld epOld ctOld] .
        have inDenI:"(type.Storage tp, Storeloc i) |\<in>| fmran (Denvalue env)"
          using denI by (simp add: fmranI)
        have oldSConE:"SCon tp i (Storage st (Address e))"
          using scOld typedOld epOld ctOld unfolding safeContract_def by blast
        have oldSCon:"SCon tp i (Storage st (Address env))"
          using oldSConE addrEq by simp
        have uniq:"unique_locations (Denvalue env)"
          using 2(1) typeSafeUnique by simp
        have epEnv:"ep $$ Contract env = Some (ct, dud)"
          using epOld addrEq
          using 2(3) fullyInitialised_def typedOld by auto
        show ?thesis
        proof(cases rule:lexpStorageG[OF 2(1) 6(2) 2(3)])
          case lInDen:1
          have inDenL:"(type.Storage t', Storeloc l) |\<in>| fmran (Denvalue env)"
            using lInDen by simp
          have cmpPtr:"(if TypedStoSubpref l i tp then CompStoType tp t' i l
                        else if TypedStoSubpref i l t' then CompStoType t' tp l i else True)"
            using 2(1) 6(3) inDenI inDenL unfolding TypeSafe_def compPointers_def by blast
          have newSCon:"SCon tp i (Storage st' (Address env))"
            using SCon_update_array_subloc_cases[OF cmpPtr SCondest2 SCondest3 oldSCon t''Def a35] .
          show ?thesis using newSCon addrEq by simp
        next
          case sub2:(2 l''' t)
          have inDenL:"(type.Storage t, Storeloc l''') |\<in>| fmran (Denvalue env)" using sub2 by simp
          have relL:"TypedStoSubpref l l''' t \<and> CompStoType t t' l''' l" using sub2 by simp
          show ?thesis
          proof(cases "i = l'''")
            case True
            have pairEq:"(type.Storage tp, Storeloc i) = (type.Storage t, Storeloc l''')"
              using uniqueLocs[OF uniq inDenI inDenL] True by simp
            then have tpEq:"tp = t" by simp
            have cmpPtr:"(if TypedStoSubpref l i tp then CompStoType tp t' i l
                          else if TypedStoSubpref i l t' then CompStoType t' tp l i else True)"
              using relL tpEq True by simp
            have newSCon:"SCon tp i (Storage st' (Address env))"
              using SCon_update_array_subloc_cases[OF cmpPtr SCondest2 SCondest3 oldSCon t''Def a35] .
            show ?thesis using newSCon addrEq by simp
          next
            case False
            have ctL:"ct $$ l''' = Some (Var t)"
              using fi_denvalue_storeloc_to_contract_var[OF 2(3) epEnv inDenL] .
            have nPrnt1:"\<not>TypedStoSubpref i l''' t"
                and nPrnt2:"\<not>TypedStoSubpref l''' i tp"
              using methodVarsNoPref False epOld ctOld ctL by blast+
            have n1:"\<not>TypedStoSubpref l i tp"
              using NotRelatedPrnt_imps_notRelatedChild[OF nPrnt1 nPrnt2] relL by blast
            have n2:"\<not>TypedStoSubpref i l t'"
              using NotReachablePrnt_imps_notReachableChild nPrnt1 nPrnt2 relL by blast
            have cmpPtr:"(if TypedStoSubpref l i tp then CompStoType tp t' i l
                          else if TypedStoSubpref i l t' then CompStoType t' tp l i else True)"
              using n1 n2 by simp
            have newSCon:"SCon tp i (Storage st' (Address env))"
              using SCon_update_array_subloc_cases[OF cmpPtr SCondest2 SCondest3 oldSCon t''Def a35] .
            show ?thesis using newSCon addrEq by simp
          qed
        next
          case sub3:(3 l' t l'')
          have inDenStk:"(type.Storage t, Stackloc l'') |\<in>| fmran (Denvalue env)" using sub3 by simp
          have ptrL:"accessStore l'' (Stack st) = Some (KStoptr l')" using sub3 by simp
          have rel0:"TypedStoSubpref l l' t \<and> CompStoType t t' l' l" using sub3 by simp
          obtain tprnt lprnt where
              inDenPr:"(type.Storage tprnt, Storeloc lprnt) |\<in>| fmran (Denvalue env)"
              and compPr:"CompStoType tprnt t lprnt l'"
            using fiPtr_parent_from_fullyInitialised[OF 2(3) inDenStk ptrL] by blast
          have compPr2:"CompStoType tprnt t' lprnt l"
            using compPr rel0 CompStoType_trns by blast
          have relPr:"TypedStoSubpref l lprnt tprnt \<and> CompStoType tprnt t' lprnt l"
            using compPr2 CompStoType_imps_TypedStoSubpref by blast
          show ?thesis
          proof(cases "i = lprnt")
            case True
            have pairEq:"(type.Storage tp, Storeloc i) = (type.Storage tprnt, Storeloc lprnt)"
              using uniqueLocs[OF uniq inDenI inDenPr] True by simp
            then have tpEq:"tp = tprnt" by simp
            have cmpPtr:"(if TypedStoSubpref l i tp then CompStoType tp t' i l
                          else if TypedStoSubpref i l t' then CompStoType t' tp l i else True)"
              using compPr2 tpEq True
              by (metis True tpEq compPr2 relPr)
            have newSCon:"SCon tp i (Storage st' (Address env))"
              using SCon_update_array_subloc_cases[OF cmpPtr SCondest2 SCondest3 oldSCon t''Def a35] .
            show ?thesis using newSCon addrEq by simp
          next
            case False
            have ctPr:"ct $$ lprnt = Some (Var tprnt)"
              using fi_denvalue_storeloc_to_contract_var[OF 2(3) epEnv inDenPr] .
            have nPrnt1:"\<not>TypedStoSubpref i lprnt tprnt"
                and nPrnt2:"\<not>TypedStoSubpref lprnt i tp"
              using methodVarsNoPref False epOld ctOld ctPr by blast+
            have n1:"\<not>TypedStoSubpref l i tp"
              using NotRelatedPrnt_imps_notRelatedChild[OF nPrnt1 nPrnt2] relPr by blast
            have n2:"\<not>TypedStoSubpref i l t'"
              using NotReachablePrnt_imps_notReachableChild nPrnt1 nPrnt2 relPr by blast
            have cmpPtr:"(if TypedStoSubpref l i tp then CompStoType tp t' i l
                          else if TypedStoSubpref i l t' then CompStoType t' tp l i else True)"
              using n1 n2 by simp
            have newSCon:"SCon tp i (Storage st' (Address env))"
              using SCon_update_array_subloc_cases[OF cmpPtr SCondest2 SCondest3 oldSCon t''Def a35] .
            show ?thesis using newSCon addrEq by simp
          qed
        qed
      qed
    qed
  next
    show "balanceTypes (Accounts st')" using 6 using 2(1) unfolding TypeSafe_def by simp
  next
    have "envAddressesWellFormed env" using 2(1) unfolding TypeSafe_def by simp
    then show "addressFormat (Address env)" and "addressFormat (Sender env)" by simp+
  next
    show "svalueTypes (Svalue env)" using 2(1) unfolding TypeSafe_def by simp
  next
    have *:"((\<forall>tloc loc. Toploc (Stack st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Stack st) = None) \<and>
            (\<forall>loc y. accessStore loc (Stack st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Stack st). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))) "
      using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by simp
    have **:"Toploc (Stack st) = Toploc (Stack st')" using 6 unfolding updateStore_def by auto
    show "lessThanTopLocs (Stack st')" using sameStack * ** unfolding lessThanTopLocs_def by auto
  next
    show "lessThanTopLocs cd" using 2(1) unfolding TypeSafe_def by simp
  next
    show "lessThanTopLocs (Memory st')" using sameMemory unfolding lessThanTopLocs_def
      by (simp add: limitSt limitSt1)
  next
    show "typeCompat (Denvalue env) (Stack st') (Memory st') (Storage st' (Address env)) cd"
      unfolding typeCompat_def
    proof intros
      fix t'' l'
      assume inDen:" (t'', l') |\<in>| fmran (Denvalue env)"

      show "denvalueCon (Stack st') (Memory st') (Storage st' (Address env)) cd t'' l'"
      proof(cases l')
        case (Stackloc x1)
        then obtain a where adef:"accessStore x1 (Stack st') = Some a" using inDen Stackloc 2(1) unfolding TypeSafe_def typeCompat_def using sameStack by fastforce
        then show ?thesis
        proof(cases "a")
          case (KValue x1)
          then show ?thesis using Stackloc adef inDen Stackloc 2(1) sameStack unfolding TypeSafe_def typeCompat_def
            by (metis (no_types, lifting) denvalue.simps(5) Option.option.simps(5) stackvalue.simps(17) )
        next
          case (KCDptr x2)
          then show ?thesis using Stackloc adef inDen Stackloc 2(1) sameStack unfolding TypeSafe_def typeCompat_def
            by (metis (no_types, lifting) denvalue.simps(5) Option.option.simps(5) stackvalue.simps(18))
        next
          case (KMemptr x3)
          then show ?thesis using Stackloc adef inDen Stackloc 2(1) sameStack sameMemory unfolding TypeSafe_def typeCompat_def by (cases t''; fastforce)
        next
          case (KStoptr x4)
          then obtain struct where structDef: "t'' = type.Storage struct" using Stackloc adef inDen Stackloc 2(1) sameStack unfolding TypeSafe_def typeCompat_def
            by (cases t''; fastforce)

          have "SCon struct x4 (Storage st' (Address env))"
          proof(cases rule:lexpStorageG[OF 2(1) 6(2) 2(3)])
            case lInDen:1
            have cmpStoPtr:"(
              (type.Storage struct, l') |\<in>| fmran (Denvalue env) \<and>
              (type.Storage (STArray x t'''), Storeloc l) |\<in>| fmran (Denvalue env) \<and>
               l' = Stackloc x1 \<and> accessStore x1 (Stack st) = Some (KStoptr x4))
               \<longrightarrow>
              (if TypedStoSubpref l x4 struct then CompStoType struct (STArray x t''') x4 l
               else if TypedStoSubpref x4 l (STArray x t''') then CompStoType (STArray x t''') struct l x4 else True)"
              using 2(1) 6(3) lInDen inDen adef Stackloc KStoptr structDef unfolding TypeSafe_def compPointers_def by blast

            then have cmpStoPtr2:"(if TypedStoSubpref l x4 struct then CompStoType struct (STArray x t''') x4 l
               else if TypedStoSubpref x4 l (STArray x t''') then CompStoType (STArray x t''') struct l x4 else True)"
              using 6(3) lInDen inDen adef Stackloc KStoptr structDef t''Def sameStack by auto

            have SConx4Old:"SCon struct x4 (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using adef Stackloc KStoptr inDen 2(1) sameStack structDef
              by fastforce

            have cmpStoPtr3:"(if TypedStoSubpref l x4 struct then CompStoType struct t' x4 l
              else if TypedStoSubpref x4 l t' then CompStoType t' struct l x4 else True)"
              using cmpStoPtr2 t''Def by fastforce
            have "SCon struct x4 (Storage st' (Address env))"
              using SCon_update_array_subloc_cases[OF cmpStoPtr3 SCondest2 SCondest3 SConx4Old t''Def a35] .
            then show ?thesis by simp
          next
            case sub2:(2 l''' t)
            have cmpStoPtr:"(
              (type.Storage struct, l') |\<in>| fmran (Denvalue env) \<and>
              (type.Storage t, Storeloc l''') |\<in>| fmran (Denvalue env) \<and>
               l' = Stackloc x1 \<and> accessStore x1 (Stack st) = Some (KStoptr x4))
               \<longrightarrow>
              (if TypedStoSubpref l''' x4 struct then CompStoType struct t x4 l'''
               else if TypedStoSubpref x4 l''' t then CompStoType t struct l''' x4 else True)"
              using 2(1) 6(3) inDen adef Stackloc KStoptr structDef unfolding TypeSafe_def compPointers_def by blast

            then have cmpStoPtr2:"(if TypedStoSubpref l''' x4 struct then CompStoType struct t x4 l'''
               else if TypedStoSubpref x4 l''' t then CompStoType t struct l''' x4 else True)"
              using 6(3) sub2 inDen adef Stackloc KStoptr structDef t''Def sameStack by auto

            have SConx4Old:"SCon struct x4 (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using adef Stackloc KStoptr inDen 2(1) sameStack structDef
              by fastforce
            have scl''':"SCon t l''' (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using sub2 by fastforce

            have "SCon struct x4 (Storage st' (Address env))"
            proof(cases "TypedStoSubpref l''' x4 struct")
              case True
              then have "CompStoType struct t x4 l'''" using cmpStoPtr2 by simp
              then have "CompStoType struct (STArray x t''') x4 l" using sub2
                using CompStoType_trns t''Def by blast
              then show ?thesis using SCondest2 SConx4Old a35 t''Def TypedStoSubpref_shared_parent_related SCon_sub_imps_Parent
                by blast
            next
              case f1:False
              then show ?thesis
              proof(cases "TypedStoSubpref x4 l''' t")
                case True
                then have "l''' \<noteq> x4" using f1
                  using TypedStoSubpref_sameLoc by auto
                then show ?thesis
                proof(cases "l = x4")
                  case t5:True
                  then have " CompStoType t struct l''' x4" using cmpStoPtr2 f1 t''Def True by simp
                  moreover have "CompStoType t t' l''' x4" using t5 sub2 by auto
                  ultimately have "t' = struct" using CompStoType_sameLocs_sameType
                    by simp
                  then show ?thesis using SCondest3 SCon_imps_sublocs t5 by simp
                next
                  case False
                  then have " CompStoType t struct l''' x4" using cmpStoPtr2 f1 t''Def True by simp
                  then show ?thesis
                  proof(cases "CompStoType t' struct l x4 ")
                    case True
                    then show ?thesis
                      using SCon_imps_sublocs SCondest3 by blast
                  next
                    case False
                    then show ?thesis
                      using SCon_imps_sublocs SCon_sub_imps_Parent SCondest2 \<open>CompStoType t struct l''' x4\<close> a35 scl''' sub2(2) t''Def by blast
                  qed
                qed
              next
                case False
                then have asm10:"\<not> TypedStoSubpref l x4 struct" using NotRelatedPrnt_imps_notRelatedChild[OF False f1 ] sub2 by blast
                then have asm20:"\<not> TypedStoSubpref x4 l t'" using sub2 NotReachablePrnt_imps_notReachableChild False f1 by blast
                have notSame:"x4 \<noteq> l" using False sub2 by blast
                have k7:"\<forall>locs. TypedStoSubpref locs x4 struct \<longrightarrow> locs \<noteq> l " using f1 sub2 asm10 asm20 by blast
                have k8:"\<forall>locs. TypedStoSubpref locs l (STArray x t''') \<longrightarrow> locs \<noteq> x4" using False sub2 t''Def asm10 asm20 by blast
                show ?thesis using sublocs_nonchanged_SCon[OF _ a35 SConx4Old] asm10 asm20 t''Def by blast
              qed
            qed

            then show ?thesis by simp
          next
            case sub3:(3 l''' t l'''')
            have cmpStoPtr:"(
              (type.Storage struct, l') |\<in>| fmran (Denvalue env) \<and>
              (type.Storage t, Stackloc l'''') |\<in>| fmran (Denvalue env) \<and>
               l' = Stackloc x1 \<and> accessStore x1 (Stack st) = Some (KStoptr x4)) \<and> accessStore l'''' (Stack st) = Some (KStoptr l''')
               \<longrightarrow>
              (if TypedStoSubpref l''' x4 struct then CompStoType struct t x4 l'''
               else if TypedStoSubpref x4 l''' t then CompStoType t struct l''' x4 else True)"
              using 2(1) 6(3) inDen adef Stackloc KStoptr structDef unfolding TypeSafe_def compPointers_def by blast

            then have cmpStoPtr2:"(if TypedStoSubpref l''' x4 struct then CompStoType struct t x4 l'''
               else if TypedStoSubpref x4 l''' t then CompStoType t struct l''' x4 else True)"
              using 6(3) sub3 inDen adef Stackloc KStoptr structDef t''Def sameStack by auto

            have SConx4Old:"SCon struct x4 (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using adef Stackloc KStoptr inDen 2(1) sameStack structDef
              by fastforce
            have scl''':"SCon t l''' (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using sub3 by fastforce

            have "SCon struct x4 (Storage st' (Address env))"
            proof(cases "TypedStoSubpref l''' x4 struct")
              case True
              then have "CompStoType struct t x4 l'''" using cmpStoPtr2 by simp
              then have "CompStoType struct (STArray x t''') x4 l" using sub3
                using CompStoType_trns t''Def by blast
              then show ?thesis using SCondest2 SConx4Old a35 t''Def TypedStoSubpref_shared_parent_related SCon_sub_imps_Parent
                by blast
            next
              case f1:False
              then show ?thesis
              proof(cases "TypedStoSubpref x4 l''' t")
                case True
                then have "l''' \<noteq> x4" using f1
                  using TypedStoSubpref_sameLoc by auto
                then show ?thesis
                proof(cases "l = x4")
                  case t5:True
                  then have " CompStoType t struct l''' x4" using cmpStoPtr2 f1 t''Def True by simp
                  moreover have "CompStoType t t' l''' x4" using t5 sub3 by auto
                  ultimately have "t' = struct" using CompStoType_sameLocs_sameType
                    by simp
                  then show ?thesis using SCondest3 SCon_imps_sublocs t5 by simp
                next
                  case False
                  then have " CompStoType t struct l''' x4" using cmpStoPtr2 f1 t''Def True by simp
                  then show ?thesis
                  proof(cases "CompStoType t' struct l x4 ")
                    case True
                    then show ?thesis
                      using SCon_imps_sublocs SCondest3 by blast
                  next
                    case False
                    then show ?thesis
                      using SCon_imps_sublocs SCon_sub_imps_Parent SCondest2 \<open>CompStoType t struct l''' x4\<close> a35 scl''' sub3(3) t''Def by blast
                  qed
                qed
              next
                case False
                then have asm10:"\<not> TypedStoSubpref l x4 struct" using NotRelatedPrnt_imps_notRelatedChild[OF False f1 ] sub3 by blast
                then have asm20:"\<not> TypedStoSubpref x4 l t'" using sub3 NotReachablePrnt_imps_notReachableChild False f1 by blast
                have notSame:"x4 \<noteq> l" using False sub3 by blast
                have k7:"\<forall>locs. TypedStoSubpref locs x4 struct \<longrightarrow> locs \<noteq> l " using f1 sub3 asm10 asm20 by blast
                have k8:"\<forall>locs. TypedStoSubpref locs l (STArray x t''') \<longrightarrow> locs \<noteq> x4" using False sub3 t''Def asm10 asm20 by blast
                show ?thesis using sublocs_nonchanged_SCon[OF _ a35 SConx4Old] asm10 asm20 t''Def by blast
              qed
            qed
            then show ?thesis by simp
          qed
          then show ?thesis using Stackloc inDen 2(1) sameStack KStoptr adef structDef by simp
        qed
      next
        case (Storeloc x2)
        then obtain struct where structDef: "t'' = type.Storage struct" using Storeloc inDen 2(1) sameStack unfolding TypeSafe_def typeCompat_def
          by (cases t''; fastforce)

        have "SCon struct x2 (Storage st' (Address env))"
        proof(cases rule:lexpStorageG[OF 2(1) 6(2) 2(3)])
          case lInDen:1
          have cmpStoPtr:"(
            (type.Storage struct, l') |\<in>| fmran (Denvalue env) \<and>
            (type.Storage (STArray x t'''), Storeloc l) |\<in>| fmran (Denvalue env) \<and>
             l' = Storeloc x2)
             \<longrightarrow>
            (if TypedStoSubpref l x2 struct then CompStoType struct (STArray x t''') x2 l
             else if TypedStoSubpref x2 l (STArray x t''') then CompStoType (STArray x t''') struct l x2 else True)"
            using 2(1) 6(3) lInDen inDen Storeloc structDef unfolding TypeSafe_def compPointers_def by blast

          then have cmpStoPtr2:"(if TypedStoSubpref l x2 struct then CompStoType struct (STArray x t''') x2 l
             else if TypedStoSubpref x2 l (STArray x t''') then CompStoType (STArray x t''') struct l x2 else True)"
            using 6(3) lInDen inDen Storeloc structDef t''Def sameStack by simp

          have SConx4Old:"SCon struct x2 (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using Storeloc inDen 2(1) sameStack structDef
            by fastforce

          have cmpStoPtr3:"(if TypedStoSubpref l x2 struct then CompStoType struct t' x2 l
            else if TypedStoSubpref x2 l t' then CompStoType t' struct l x2 else True)"
            using cmpStoPtr2 t''Def by fastforce
          have "SCon struct x2 (Storage st' (Address env))"
            using SCon_update_array_subloc_cases[OF cmpStoPtr3 SCondest2 SCondest3 SConx4Old t''Def a35] .
          then show ?thesis by simp
        next
          case sub2:(2 l''' t)
          have cmpStoPtr:"(
              (type.Storage struct, Storeloc x2) |\<in>| fmran (Denvalue env) \<and>
              (type.Storage t, Storeloc l''') |\<in>| fmran (Denvalue env) )
               \<longrightarrow>
              (if TypedStoSubpref l''' x2 struct then CompStoType struct t x2 l'''
               else if TypedStoSubpref x2 l''' t then CompStoType t struct l''' x2 else True)"
            using 2(1) 6(3) inDen Storeloc structDef unfolding TypeSafe_def compPointers_def by blast

          then have cmpStoPtr2:"(if TypedStoSubpref l''' x2 struct then CompStoType struct t x2 l'''
               else if TypedStoSubpref x2 l''' t then CompStoType t struct l''' x2 else True)"
            using 6(3) sub2 inDen Storeloc structDef t''Def sameStack by auto

          have SConx4Old:"SCon struct x2 (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using Storeloc inDen 2(1) sameStack structDef
            by fastforce
          have scl''':"SCon t l''' (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using sub2 by fastforce

          have "SCon struct x2 (Storage st' (Address env))"
          proof(cases "TypedStoSubpref l''' x2 struct")
            case True
            then have "CompStoType struct t x2 l'''" using cmpStoPtr2 by simp
            then have "CompStoType struct (STArray x t''') x2 l" using sub2
              using CompStoType_trns t''Def by blast
            then show ?thesis using SCondest2 SConx4Old a35 t''Def TypedStoSubpref_shared_parent_related SCon_sub_imps_Parent
              by blast
          next
            case f1:False
            then show ?thesis
            proof(cases "TypedStoSubpref x2 l''' t")
              case True
              then have "l''' \<noteq> x2" using f1
                using TypedStoSubpref_sameLoc by auto
              then show ?thesis
              proof(cases "l = x2")
                case t5:True
                then have " CompStoType t struct l''' x2" using cmpStoPtr2 f1 t''Def True by simp
                moreover have "CompStoType t t' l''' x2" using t5 sub2 by auto
                ultimately have "t' = struct" using CompStoType_sameLocs_sameType
                  by simp
                then show ?thesis using SCondest3 SCon_imps_sublocs t5 by simp
              next
                case False
                then have " CompStoType t struct l''' x2" using cmpStoPtr2 f1 t''Def True by simp
                then show ?thesis
                proof(cases "CompStoType t' struct l x2 ")
                  case True
                  then show ?thesis
                    using SCon_imps_sublocs SCondest3 by blast
                next
                  case False
                  then show ?thesis
                    using SCon_imps_sublocs SCon_sub_imps_Parent SCondest2 \<open>CompStoType t struct l''' x2\<close> a35 scl''' sub2(2) t''Def by blast
                qed
              qed
            next
              case False
              then have asm10:"\<not> TypedStoSubpref l x2 struct" using NotRelatedPrnt_imps_notRelatedChild[OF False f1 ] sub2 by blast
              then have asm20:"\<not> TypedStoSubpref x2 l t'" using sub2 NotReachablePrnt_imps_notReachableChild False f1 by blast
              have notSame:"x2 \<noteq> l" using False sub2 by blast
              have k7:"\<forall>locs. TypedStoSubpref locs x2 struct \<longrightarrow> locs \<noteq> l " using f1 sub2 asm10 asm20 by blast
              have k8:"\<forall>locs. TypedStoSubpref locs l (STArray x t''') \<longrightarrow> locs \<noteq> x2" using False sub2 t''Def asm10 asm20 by blast
              show ?thesis using sublocs_nonchanged_SCon[OF _ a35 SConx4Old] asm10 asm20 t''Def by blast
            qed
          qed

          then show ?thesis by simp
        next
          case sub3:(3 l''' t l'''')
          have cmpStoPtr:"(
              (type.Storage struct, Storeloc x2) |\<in>| fmran (Denvalue env) \<and>
              (type.Storage t, Stackloc l'''') |\<in>| fmran (Denvalue env) \<and>
               accessStore l'''' (Stack st) = Some (KStoptr l'''))
               \<longrightarrow>
              (if TypedStoSubpref l''' x2 struct then CompStoType struct t x2 l'''
               else if TypedStoSubpref x2 l''' t then CompStoType t struct l''' x2 else True)"
            using 2(1) 6(3) inDen Storeloc structDef unfolding TypeSafe_def compPointers_def by blast

          then have cmpStoPtr2:"(if TypedStoSubpref l''' x2 struct then CompStoType struct t x2 l'''
               else if TypedStoSubpref x2 l''' t then CompStoType t struct l''' x2 else True)"
            using 6(3) sub3 inDen Storeloc structDef t''Def sameStack by auto

          have SConx4Old:"SCon struct x2 (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using Storeloc inDen 2(1) sameStack structDef
            by fastforce
          have scl''':"SCon t l''' (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using sub3 by fastforce

          have "SCon struct x2 (Storage st' (Address env))"
          proof(cases "TypedStoSubpref l''' x2 struct")
            case True
            then have "CompStoType struct t x2 l'''" using cmpStoPtr2 by simp
            then have "CompStoType struct (STArray x t''') x2 l" using sub3
              using CompStoType_trns t''Def by blast
            then show ?thesis using SCondest2 SConx4Old a35 t''Def TypedStoSubpref_shared_parent_related SCon_sub_imps_Parent
              by blast
          next
            case f1:False
            then show ?thesis
            proof(cases "TypedStoSubpref x2 l''' t")
              case True
              then have "l''' \<noteq> x2" using f1
                using TypedStoSubpref_sameLoc by auto
              then show ?thesis
              proof(cases "l = x2")
                case t5:True
                then have " CompStoType t struct l''' x2" using cmpStoPtr2 f1 t''Def True by simp
                moreover have "CompStoType t t' l''' x2" using t5 sub3 by auto
                ultimately have "t' = struct" using CompStoType_sameLocs_sameType
                  by simp
                then show ?thesis using SCondest3 SCon_imps_sublocs t5 by simp
              next
                case False
                then have " CompStoType t struct l''' x2" using cmpStoPtr2 f1 t''Def True by simp
                then show ?thesis
                proof(cases "CompStoType t' struct l x2 ")
                  case True
                  then show ?thesis
                    using SCon_imps_sublocs SCondest3 by blast
                next
                  case False
                  then show ?thesis
                    using SCon_imps_sublocs SCon_sub_imps_Parent SCondest2 \<open>CompStoType t struct l''' x2\<close> a35 scl''' sub3(3) t''Def by blast
                qed
              qed
            next
              case False
              then have asm10:"\<not> TypedStoSubpref l x2 struct" using NotRelatedPrnt_imps_notRelatedChild[OF False f1 ] sub3 by blast
              then have asm20:"\<not> TypedStoSubpref x2 l t'" using sub3 NotReachablePrnt_imps_notReachableChild False f1 by blast
              have notSame:"x2 \<noteq> l" using False sub3 by blast
              have k7:"\<forall>locs. TypedStoSubpref locs x2 struct \<longrightarrow> locs \<noteq> l " using f1 sub3 asm10 asm20 by blast
              have k8:"\<forall>locs. TypedStoSubpref locs l (STArray x t''') \<longrightarrow> locs \<noteq> x2" using False sub3 t''Def asm10 asm20 by blast
              show ?thesis using sublocs_nonchanged_SCon[OF _ a35 SConx4Old] asm10 asm20 t''Def by blast
            qed
          qed
          then show ?thesis by simp
        qed


        then show ?thesis using Storeloc inDen 2(1) sameStack Storeloc structDef by simp
      qed
    qed
    then have "typeCompat (Denvalue env) (Stack st) (Memory st') (Storage st' (Address env)) cd" using sameStack by simp

  next
    have "Accounts st'= Accounts st" using 6 by auto
    then show "fullyInitialised env (Accounts st') (Stack st')" using 2(3) 6 unfolding fullyInitialised_def by auto
  next
    have ss:"Stack st = Stack st' \<and> Memory st = Memory st'" using 6 by simp
    have cc0:"\<forall>l ptr_loc. accessStore l (Stack st') = Some (KMemptr ptr_loc) \<longrightarrow> accessStore l (Stack st) = Some (KMemptr ptr_loc)"
      using 6(5) unfolding updateStore_def accessStore_def by auto
    have sameMem:"Memory st = Memory st'" using 6(5) by simp
    show "denvalueTypeCorrectness env (Stack st') (Memory st')"
      unfolding denvalueTypeCorrectness_def
    proof intros
      fix t l ptr_loc
      assume "(type.Memory t, Stackloc l) |\<in>| fmran (Denvalue env) \<and>
     accessStore l (Stack st') = Some (KMemptr ptr_loc)"
      then have "(case t of
       MTArray len arr \<Rightarrow> (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr)
       | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st) = Some (MTValue val))"
        using 2(1) unfolding TypeSafe_def denvalueTypeCorrectness_def using cc0 by blast
      then show "case t of
     MTArray len arr \<Rightarrow> (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr)
     | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st') = Some (MTValue val)"
        using sameMem by metis
    qed
  next
    have sameMem:"Memory st = Memory st'" using 6(5) by simp
    show "subPrefixStructuralConsistency (Memory st')"
      using 2(1) sameMem unfolding TypeSafe_def by simp
  next
    show "SomeValSomeTyp (Memory st')" using 2(1) unfolding TypeSafe_def using 6(5) by auto
  next
    show "\<And>locs t. accessTypeStore locs (Memory st) = Some t \<Longrightarrow> accessTypeStore locs (Memory st') = Some t"
      using 6(5) by auto
  next
    show "\<And>locs v. accessStore locs (Memory st) = Some (MPointer v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MPointer v')"
      using 6(5) by simp
  next
    show "\<And>locs v. accessStore locs (Memory st) = Some (MValue v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MValue v')"
      using 6(5) by simp
  next
    show " \<And>i loc. i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<Longrightarrow> accessStore loc
        (Memory st) = None \<Longrightarrow> accessStore loc (Memory st') = None"
      using 6(5) by simp
  next
    show "Toploc (Memory st) \<le> Toploc (Memory st')" using 6(5) by auto
  qed
qed

text \<open>Assignment case 7: a calldata array assigned to a memory location: the array is copied into fresh memory and the location is updated to point to it.\<close>

lemma TypeSafe_Assign_7:
  assumes "TypeSafe env (Accounts st) (Stack st) (Memory st) (Storage st) cd"
    and "stmt (ASSIGN lv ex) env cd st = Normal ((), st')"
    and "fullyInitialised env (Accounts st) (Stack st)"
    and "expr ex env cd (st\<lparr>state.Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>) (state.Gas st - costs (ASSIGN lv
        ex) env cd st) = Normal ((KCDptr p, Calldata (MTArray x t)), g)"
    and "lexp lv env cd (st\<lparr>state.Gas := g\<rparr>) g = Normal((LMemloc l, type.Memory t'),g')"
    and "(MTArray x t) = t'"
    and "cpm2m p (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) x t cd (snd (allocate (Memory st))) = Some m"
    and "(updateStore l (MPointer (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))) m) = m'"
    and "st' = st\<lparr>state.Gas := g', Memory := m'\<rparr>"
  shows "StateInvariant env st st' cd"
proof -
  let ?case = "StateInvariant env st st' cd"
  note 2 = assms(1-3)
  note 7 = assms(4-9)
  have temp:"TypeSafe env (Accounts (st\<lparr>Gas := g\<rparr>)) (Stack (st\<lparr>Gas := g\<rparr>)) (Memory (st\<lparr>Gas := g\<rparr>)) (Storage (st\<lparr>Gas := g\<rparr>)) cd"
    using 2(1) by simp
  have ttt:"fullyInitialised env (Accounts (st\<lparr>Gas := g\<rparr>)) (Stack (st\<lparr>Gas := g\<rparr>))" using 2(3) unfolding fullyInitialised_def by simp
  then show ?thesis
  proof(cases rule:lexpIndexMem[OF 7(2) temp ttt])
    case lInfo:(1 x21 x22 tp tParent l' l'' prnt len' arr' i)
    have nonChangedStack:"\<forall>loc. loc \<noteq> l \<longrightarrow> accessStore loc (Stack st) = accessStore loc (Stack st')" using 7 unfolding accessStore_def updateStore_def by auto
    have sameStack:"(Stack st') = Stack st" using 7 unfolding accessStore_def updateStore_def by auto
    have sameStorage:"Storage st' = Storage st " using 7 by auto
    have nonLocChanged:"\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<or> locs =
        (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))\<longrightarrow> accessStore locs (snd (allocate (Memory st))) = accessStore
        locs m"
      using 7(4) unfolding cpm2m_def using cpm2mSingleChange[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd " (snd
          (allocate (Memory st)))" x m ] cpm2m_def[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" x t cd " (snd (allocate
          (Memory st)))" ]
      by fastforce
    have a30:"\<forall>locs. \<not> TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x t)
        \<longrightarrow> accessStore locs (snd (allocate (Memory st))) = accessStore locs m"
      using 7(4) unfolding cpm2m_def using cpm2mSingleChange_typedPref[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd " (snd (allocate (Memory st)))" x m ] by fastforce
    have a32:"\<forall>locs. \<not> TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x t) \<longrightarrow> accessStore locs (Memory st) = accessStore locs m"
      by (metis a30 allocateSameAccess)
    have selfPoint:"\<forall>l l'. TypedMemSubPref l (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x t) \<and> accessStore
        l m = Some (MPointer l') \<longrightarrow> l' = l \<and> l \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))"
      using 7(4) unfolding cpm2m_def using cpm2mSelfPointers[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd " (snd (allocate (Memory st)))" x m ]
      by (metis LSubPrefL2_def hash_inequality hash_suffixes_associative TypedMemSubPref.simps(2) typedPrefix_imp_SubPref)

    have sameTypeAccess:" \<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<or> locs =
        (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow>
     accessTypeStore locs (Memory st) = accessTypeStore locs m"
      using 7(4) unfolding cpm2m_def
      using cpm2mSingleChange_Typed[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd " (snd (allocate (Memory st)))" x m ]
        allocateTypeSameAccess by metis

    have sameTypeAccess2:" \<forall>locs. \<not> TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x t)
        \<or> locs = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow>
     accessTypeStore locs (Memory st) = accessTypeStore locs m"
      using 7(4) unfolding cpm2m_def
      using cpm2mSingleChange_typedPref_typed[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd " (snd (allocate (Memory st)))" x m ]
        allocateTypeSameAccess by metis

    have mInStd:"m' = Memory st'" using 7 by simp
    have NonChangeM'm:"\<forall>locs. locs \<noteq> l \<longrightarrow> accessStore locs m = accessStore locs m'"
      using 7(5) unfolding accessStore_def updateStore_def by auto
    have NonChangeM'mT:"\<forall>locs. accessTypeStore locs m = accessTypeStore locs m'"
      using 7(5) unfolding accessStore_def updateStore_def accessTypeStore_def by auto
    then have nonLocChanged3:"\<forall>locs. locs \<noteq>l \<and> \<not> TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x t)
                              \<longrightarrow> accessStore locs (Memory st) = accessStore locs (Memory st')"
      using a32 mInStd NonChangeM'm by auto

    have accessL:"accessStore l m' = Some (MPointer (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))))" using 7(5) unfolding accessStore_def updateStore_def by auto

    have MConsrc:"MCon (MTArray x t) cd (extractValueType (KCDptr p)) \<and> (\<exists>xx. KCDptr p = KCDptr xx) \<and>
          (\<exists>stloc tp'' pa.
          (Calldata tp'', Stackloc stloc) |\<in>| fmran (Denvalue env) \<and>
          accessStore stloc (Stack (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)) = Some (KCDptr pa) \<and>
          (tp'' = (MTArray x t) \<and> KCDptr p = KCDptr pa \<or>
           (\<exists>len arr. extractValueType (KCDptr p) \<noteq> pa \<and> tp'' = MTArray len arr \<and> CompMemType cd len arr (MTArray x t) pa (extractValueType (KCDptr p)))))"
      using 2(1) 7(1) exprTypeconInduct(3)[of ex env cd "(st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)"
          "(state.Gas st - costs (ASSIGN lv ex) env cd st)" "KCDptr p" "Calldata (MTArray x t)" g]
      using 2(3) unfolding fullyInitialised_def
      by (auto split:type.splits if_splits )

    have limitSt1:"(\<forall>loc y. accessStore loc (Memory st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Memory st). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))"
      using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by simp
    have limitSt:"(\<forall>tloc loc. Toploc (Memory st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Memory st) = None)"
      using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by simp
    moreover have allocateSame:"\<forall>loc. accessStore loc (Memory st) = accessStore loc (snd (allocate (Memory st)))"
      using allocateSameAccess by blast
    ultimately have "accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (snd (allocate (Memory st))) = None" using LSubPrefL2_def by auto
    then have MCondest:" MCon (MTArray x t) m (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" using 7(4) unfolding cpm2m_def
      using MCon_cpm2m[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd "(snd (allocate (Memory st)))" x m]
        MConsrc extractValueType.simps(2) by metis
    have lIs:"\<exists>x. accessStore l (Memory st) = Some x" using lInfo by (auto split:option.splits)
    then have lOld:"\<exists>p. accessStore l (Memory st) = Some (MPointer p)" using lInfo 7 by force
    then have l_not_toploc_orSub:"\<not>LSubPrefL2 l (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))"
      using limitSt by fastforce
    then have lOld2:"\<exists>p. accessStore l m = Some (MPointer p)" using lOld
      by (simp add: allocateSame nonLocChanged)


    have tps:"\<forall>destl'.
   TypedMemSubPref destl' (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x t) \<longrightarrow>
   (\<exists>stt. CompMemType m x t stt (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) destl' \<and>
         (case stt of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some parent_arr
          | MTValue pval \<Rightarrow> accessTypeStore destl' m = Some (MTValue pval)))"
      using 7(4) unfolding cpm2m_def
      using cpm2m_TypeCompChange[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd "(snd (allocate (Memory st)))" x m] by simp

    have tps2:"\<forall>i<x. accessTypeStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some t"
      using 7(4) unfolding cpm2m_def
      using cpm2m_TypeCompChangeIndexs[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd "(snd (allocate (Memory st)))" x m]
      by blast

    have selfPoint2:"\<forall>l1 l2. LSubPrefL2 l1 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))
                      \<and> accessStore l1 (Memory st') = Some (MPointer l2) \<longrightarrow> l2 = l1 \<and> l1 \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))"
      by (metis NonChangeM'm a30 allocateSame l_not_toploc_orSub limitSt linorder_le_cases mInStd option.distinct(1)
          selfPoint)

    obtain len subT where tParentType:"tParent = MTArray len subT" using lInfo by blast
    then obtain p'' where lOrigin:"accessStore l (Memory (st)) = Some (MPointer p'')"
        and compType:"CompMemType (Memory (st\<lparr>Gas := g\<rparr>)) len subT (MTArray x t) l'' p''"
        and lsublocs:"l = hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<and> i < len' \<and> arr' = (MTArray x t) \<and> MCon (MTArray len' arr') (Memory (st)) prnt"
        and lsublocs3:"(prnt = l'' \<and> len = len' \<and> arr' = subT \<or> CompMemType (Memory (st)) len subT (MTArray len' arr') l'' prnt)"
      using lInfo 7(3) by force
    then have lsublocs2:" CompMemType (Memory (st)) len' arr' (MTArray x t) prnt p''"
      using "7"(3) CompMemType.simps(2) by blast

    then have bb9:"\<forall>subT subloc. CompMemType (Memory (st)) len' arr' subT prnt subloc \<and> subloc = p''
                                \<longrightarrow> subT = (MTArray x t)"
      using CompMemTypeSameLocsSameType lsublocs by blast

    have mconPrnt:"MCon (MTArray len' (MTArray x t)) (Memory st) prnt" using lsublocs by auto
    have ldef:"l = hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<and> i < len'" using lsublocs by auto

    have t6:"(type.Memory tParent, Stackloc l') |\<in>| fmran (Denvalue env)" using lInfo by blast
    have t7:" MCon (MTArray len subT) (Memory (st)) l''" using lInfo
      using tParentType by auto
    then have t8:"\<not> LSubPrefL2 l'' (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" using limitSt limitSt1 typeSafe_noDenElementOverToploc_mem[OF 2(1) t6] lInfo(3) by simp
    have comptype2:"CompMemType m len subT (MTArray x t) l'' p''" using
        cpm2mCompMemTypeOld_imps_CompMemType[of "(Memory (st\<lparr>Gas := g\<rparr>))" len subT "(MTArray x t)" l'' p'' "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" m ]
        compType nonLocChanged limitSt t7 t8 allocateSame by auto
    have t10:"CompMemType (Memory st) len subT (MTArray x t) l'' p''"
      using
        cpm2mCompMemTypeOld_imps_CompMemType[of "(Memory (st\<lparr>Gas := g\<rparr>))" len subT "(MTArray x t)" l'' p'' "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" m ]
        compType nonLocChanged limitSt t7 t8 allocateSame by auto
    then have mconlOld:"MCon (MTArray x t) (Memory st) p''" using 7(3) lInfo lOrigin by force

    have den:"(type.Memory (MTArray len subT), Stackloc l') |\<in>| fmran (Denvalue env)
            \<and> accessStore l' (Stack st) = Some (KMemptr l'')" using lInfo tParentType by simp
    have nonLocChanged_TypedSafe:"\<forall>loc. \<not> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))
                                        \<longrightarrow> accessTypeStore loc (Memory st') = accessTypeStore loc (Memory st)"
    proof -
      have "\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<or> locs =
          (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow> accessTypeStore locs (snd (allocate (Memory st))) =
          accessTypeStore locs m"
        using 7(4,5,6) cpm2mSingleChange_Typed[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd " (snd (allocate (Memory st)))" x m ]
          cpm2m_def[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" x t cd " (snd (allocate (Memory st)))" ] by simp
      then have "\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<or> locs =
          (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow> accessTypeStore locs (snd (allocate (Memory st))) =
          accessTypeStore locs m'"
        using 7(6,5) unfolding accessTypeStore_def updateStore_def by force
      then show "\<forall>loc. \<not> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow> accessTypeStore loc (Memory st') = accessTypeStore loc (Memory st)"
        using allocateTypeSameAccess mInStd by metis
    qed


    have nonLocChanged2:"\<forall>locs. locs \<noteq> l \<and> \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))
        \<longrightarrow> accessStore locs (Memory st) = accessStore locs (Memory st')"
      using 7 nonLocChanged LSubPrefL2_def NonChangeM'm mInStd allocateSame by metis
    have stackDenvalLimits:"\<forall>struct loc stloc. (type.Memory struct, Stackloc loc) |\<in>| fmran (Denvalue env)
                        \<and> accessStore loc (Stack st) = Some (KMemptr stloc) \<longrightarrow> \<not> LSubPrefL2 stloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))"
      using typeSafe_noDenElementOverToploc_mem[OF 2(1)] by auto
    have MCondest2:" MCon (MTArray x t) (Memory st') (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) " using 7 MCondest
    proof -
      have "\<not> LSubPrefL2 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) l"
        using l_not_toploc_orSub MemLSubPrefTransitive LSubPrefL2_refl by blast
      moreover have "\<forall>d. \<not> LSubPrefL2 d l \<longrightarrow> accessStore d m = accessStore d (Memory st')"
        using NonChangeM'm mInStd LSubPrefL2_refl by metis
      ultimately show ?thesis
        using MCon_mem_preserved_disjoint_update[of "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" l "MTArray x t" m "Memory st'"] selfPoint l_not_toploc_orSub MCondest by blast
    qed
    have bb:"\<forall>locs tp. CompMemType (Memory st) len subT tp l'' locs \<longrightarrow> locs \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t
        (Toploc (Memory st))) \<and> \<not>LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))"
    proof intros
      fix locs tp
      assume asm1:"CompMemType (Memory st) len subT tp l'' locs"
      then have a2:"locs \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" using t7
      proof(induction subT arbitrary:len l'')
        case (MTArray x1 subT)
        then show ?case
          using CompMemType_imps_TypedMemSubPrefPtrs LSubPrefL2_def limitSt limitSt1 subPtrs_nonTop by blast
      next
        case (MTValue x)
        then show ?case
          by (metis (no_types, lifting) CompMemType_imps_TypedMemSubPrefPtrs LSubPrefL2_def limitSt limitSt1 subPtrs_nonTop)
      qed
      then show " locs \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" by simp
      show "\<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) " using a2 by simp
    qed

    have nonLocChanged22:"\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<or> locs = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))
                          \<longrightarrow> accessStore locs (Memory st) = accessStore locs m" using nonLocChanged
      by (simp add: allocateSame)

    have prntMconNew:"MCon (MTArray len' (MTArray x t)) (Memory st') prnt"
    proof -
      have " \<forall>i<len'.
           (case accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') of None \<Rightarrow> False
            | Some (MValue val) \<Rightarrow> (case MTArray x t of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon
                (MTArray x t) (Memory st') (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
            | Some (MPointer loc2) \<Rightarrow> (case MTArray x t of MTArray len' arr' \<Rightarrow> MCon (MTArray x t) (Memory st') loc2 | MTValue Types \<Rightarrow> False))"
      proof intros
        fix i' assume asm1:"i'<len'"
        then obtain ptr where ptrDef': "accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (Memory st) = Some(MPointer ptr)
                                " and ptrDef'2:"MCon (MTArray x t) (Memory st) ptr"
          using mconPrnt by (metis MConArrayPointers MCon_imps_sub_Mcon bot_nat_0.not_eq_extremum not_less_zero)

        show "case accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (Memory st') of None \<Rightarrow> False
            | Some (MValue val) \<Rightarrow> (case MTArray x t of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon
                (MTArray x t) (Memory st') (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i')))
            | Some (MPointer loc2) \<Rightarrow> (case MTArray x t of MTArray len' arr' \<Rightarrow> MCon (MTArray x t) (Memory st') loc2 | MTValue Types \<Rightarrow> False)"
        proof(cases "i' = i")
          case True
          then show ?thesis
            using MCondest2 accessL ldef mInStd by force
        next
          case False
          then have "accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (Memory st) = accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (Memory st')" using ldef
            by (metis hashesIntSame limitSt nle_le nonLocChanged2 option.distinct(1) ptrDef')
          then have same:"accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (Memory st') = Some(MPointer ptr)" using ptrDef' by simp
          have notPrnt:"ptr \<noteq> prnt"
            using MConSubTypes mconPrnt ptrDef' CompMemJustType.simps(2) ptrDef'2 by blast

          have locRule:"\<forall>ct locs ints. CompMemType (Memory st) len' (MTArray x t) ct prnt locs \<longrightarrow> locs \<noteq>
              prnt \<and> hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t ints) \<noteq> l"
            using BothMConImpsNotCompMemType CompTypeRemainsMCon mconPrnt ldef ShowLNatDot hash_injective by metis
          have "CompMemType (Memory st) len' (MTArray x t) (MTArray x t) prnt ptr" using ptrDef' asm1 by auto
          then have "MCon (MTArray x t) (Memory st') ptr" using ptrDef'2 locRule
          proof(induction t arbitrary: x ptr len' prnt)
            case (MTArray x11 x12)
            have "\<forall>i<x. (case accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') of None \<Rightarrow> False
             | Some (MValue val) \<Rightarrow> (case MTArray x11 x12 of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon
                 (MTArray x11 x12) (Memory st') (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
             | Some (MPointer loc2) \<Rightarrow> (case MTArray x11 x12 of MTArray len' arr' \<Rightarrow> MCon (MTArray x11 x12) (Memory st') loc2 | MTValue Types \<Rightarrow> False))"
            proof intros
              fix i'' assume "i''<x"
              then obtain ptr' where ptr'Def:"accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st) = Some(MPointer ptr')
                                              \<and> MCon (MTArray x11 x12) (Memory st) ptr'" using MTArray.prems(2)
                by (metis MConArrayPointers MCon_imps_sub_Mcon neq0_conv not_less_zero)
              have "ptr \<noteq> prnt" using MTArray.prems by blast
              then have "(hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) \<noteq> l" using MTArray.prems ShowLNatDot hash_injective by blast
              then have "accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st) = accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st')"
                by (metis less_or_eq_imp_le limitSt nonLocChanged2 option.discI ptr'Def)
              then have same2:"accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st') = Some(MPointer ptr')" using ptr'Def by simp

              have "MCon (MTArray x11 x12) (Memory st) ptr'" using ptr'Def by blast
              moreover have "CompMemType (Memory st) x (MTArray x11 x12) (MTArray x11 x12) ptr ptr'" using ptr'Def
                using \<open>i'' < x\<close> by auto
              moreover have "\<forall>ct locs ints. CompMemType (Memory st) x (MTArray x11 x12) ct ptr locs \<longrightarrow> locs
                  \<noteq> ptr \<and> hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t ints) \<noteq> l"
                by (metis BothMConImpsNotCompMemType CompTypeRemainsMCon MTArray.prems(1,2,3) compMemTypes_trns)
              ultimately have "MCon (MTArray x11 x12) (Memory st') ptr'" using MTArray.IH[of x x11 ptr ptr'] by blast
              then show "(case accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st') of None \<Rightarrow> False
             | Some (MValue val) \<Rightarrow> (case MTArray x11 x12 of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon
                 (MTArray x11 x12) (Memory st') (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i'')))
             | Some (MPointer loc2) \<Rightarrow> (case MTArray x11 x12 of MTArray len' arr' \<Rightarrow> MCon (MTArray x11 x12) (Memory st') loc2 | MTValue Types \<Rightarrow> False))"
                using ptrDef' same2 by auto
            qed

            moreover have xNotZero:"x>0" using MTArray.prems(2)
              using bot_nat_0.not_eq_extremum by fastforce
            moreover have "(\<exists>p. accessStore ptr (Memory st') = Some (MPointer p)) \<or> accessStore ptr (Memory st') = None"
            proof(cases "ptr = l")
              case True
              then have " accessStore ptr (Memory st') = Some (MPointer (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))))" using 7 by auto
              then show ?thesis by blast
            next
              case False
              then have pdef:"(\<exists>p. accessStore ptr (Memory st) = Some (MPointer p)) \<or> accessStore ptr (Memory st) = None"
                using MTArray.prems(2) MCon.simps(2)[of x _ "Memory st" ptr] xNotZero by simp
              then have "\<not> LSubPrefL2 ptr (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" using limitSt1 limitSt
                by (metis (no_types, lifting) MCon_imps_Some MTArray.prems(2) LSubPrefL2_def Not_Sub_More_Specific le_refl option.distinct(1))
              then have "accessStore ptr (Memory st) =accessStore ptr (Memory st') " using False nonLocChanged2 by simp
              then show ?thesis using pdef by simp
            qed
            ultimately show ?case using MCon.simps(2)[of x "MTArray x11 x12" "Memory st'" ptr] by simp
          next
            case (MTValue x2)
            have "\<forall>i<x. (case accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') of None \<Rightarrow> False
               | Some (MValue val) \<Rightarrow> (case MTValue x2 of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon
                   (MTValue x2) (Memory st') (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
               | Some (MPointer loc2) \<Rightarrow> (case MTValue x2 of MTArray len' arr' \<Rightarrow> MCon (MTValue x2) (Memory st') loc2 | MTValue Types \<Rightarrow> False))"
            proof intros
              fix i'' assume "i''<x"
              then obtain val where oldDef:"accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st) = Some(MValue val)
                                              \<and> MCon (MTValue x2) (Memory st) (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i''))" using MTValue ptrDef'
                by (meson MCon_imps_sub_Mcon MCon_sub_MTVal_imps_val)
              have "(hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) \<noteq> l " using MTValue ldef ShowLNatDot hash_injective by blast
              then have "accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st) = accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st')"
                by (metis less_or_eq_imp_le limitSt nonLocChanged2 option.discI oldDef)
              then have "accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st') = Some(MValue val)" using oldDef by simp
              then show "case accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st') of None \<Rightarrow> False
                     | Some (MValue val) \<Rightarrow> (case MTValue x2 of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow>
                         MCon (MTValue x2) (Memory st') (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i'')))
                     | Some (MPointer loc2) \<Rightarrow> (case MTValue x2 of MTArray len' arr' \<Rightarrow> MCon (MTValue x2) (Memory st') loc2 | MTValue Types \<Rightarrow> False)"
                using oldDef by auto
            qed
            moreover have xNotZero:"x>0" using MTValue(2)
              using bot_nat_0.not_eq_extremum by fastforce
            moreover have "(\<exists>p. accessStore ptr (Memory st') = Some (MPointer p)) \<or> accessStore ptr (Memory st') = None"
            proof(cases "ptr = l")
              case True
              then have " accessStore ptr (Memory st') = Some (MPointer (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))))" using 7 by auto
              then show ?thesis by blast
            next
              case False
              then have pdef:"(\<exists>p. accessStore ptr (Memory st) = Some (MPointer p)) \<or> accessStore ptr (Memory st) = None"
                using MTValue(2) MCon.simps(2)[of x _ "Memory st" ptr] xNotZero by simp
              then have "\<not> LSubPrefL2 ptr (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" using limitSt1 limitSt
                by (metis (no_types, lifting) MCon_imps_Some MTValue(2) LSubPrefL2_def Not_Sub_More_Specific le_refl option.distinct(1))
              then have "accessStore ptr (Memory st) =accessStore ptr (Memory st') " using False nonLocChanged2 by simp
              then show ?thesis using pdef by simp
            qed

            ultimately show ?case using MCon.simps(2)[of x "MTValue x2" "Memory st'" ptr] by simp
          qed
          then show ?thesis using same asm1 by simp
        qed
      qed

      moreover have "len' > 0" using mconPrnt
        using ldef by auto
      moreover have "prnt \<noteq> l" using ldef
        by (metis hash_inequality)
      moreover have "(\<exists>p. accessStore prnt (Memory st') = Some (MPointer p)) \<or> accessStore prnt (Memory st') = None"
      proof(cases "LSubPrefL2 prnt (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))")
        case True
        then show ?thesis
          by (metis LSubPrefL2_def Not_Sub_More_Specific l_not_toploc_orSub ldef)
      next
        case False
        then show ?thesis using nonLocChanged2 calculation mconPrnt by simp
      qed
      ultimately show ?thesis using MCon.simps(2)[of len' "MTArray x t" "Memory st'" prnt] mconPrnt nonLocChanged2 ldef by simp
    qed


    then have l''Top'':"CompMemType (Memory (st)) len subT (MTArray x t) l'' p''" using lsublocs3 lsublocs
      using compMemTypes_trns lsublocs2 by blast


    have aaa:"\<forall>sT sL. CompMemType (Memory (st)) len subT sT
        l'' sL \<and> sL \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> \<not> LSubPrefL2 sL
            (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> MCon (MTArray len subT) (Memory (st)) l''
                          \<longrightarrow> CompMemType m len subT sT l'' sL"
    proof(intros)
      fix sT sL
      assume asm1: " CompMemType (Memory st) len subT sT
          l'' sL \<and> sL \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> \<not> LSubPrefL2 sL
              (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> MCon (MTArray len subT) (Memory (st)) l''"
      then show " CompMemType m len subT sT l'' sL"
      proof(induction subT arbitrary: len l'')
        case (MTArray x1 subT)
        obtain i'' ptr where i''Def:"(i''<len \<and> accessStore (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st) = Some
            (MPointer ptr) \<and> (ptr = sL \<and> MTArray x1 subT = sT \<or> CompMemType (Memory st) x1 subT sT ptr sL))"
          using MTArray.prems unfolding CompMemType.simps by auto
        then have "accessStore (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st) = accessStore (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) m" using MTArray.prems
          by (metis Read_Show_nat'_id antisym_conv1 limitSt nonLocChanged22 option.distinct(1) readLintNotEqual)

        then show ?case
        proof(cases "ptr = sL")
          case True
          then have "MTArray x1 subT = sT" using i''Def MTArray.prems
            by (meson BothMConImpsNotCompMemType CompTypeRemainsMCon MCon_imps_sub_Mcon)
          then show ?thesis using True i''Def
            using \<open>accessStore (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st) = accessStore (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) m\<close> by force
        next
          case False
          then have "CompMemType m x1 subT sT ptr sL" using MTArray.IH[of x1 ptr] using i''Def MTArray.prems by force
          then show ?thesis
            by (metis \<open>accessStore (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st) = accessStore (hash l''
                (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) m\<close> i''Def CompMemType.simps(2))
        qed
      next
        case (MTValue x)
        then show ?case
          by auto
      qed
    qed


    have BT3:"\<forall>locs tp x t. \<not>LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow>
        \<not>CompMemType (Memory (st')) x t tp (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) locs
                                                                  \<and> \<not>TypedMemSubPrefPtrs (Memory (st')) x t (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) locs"
      using CompMemType_imps_TypedMemSubPrefPtrs LSubPrefL2_def SubPtrs_top selfPoint2 by blast

    have accessLGen:"\<exists>ptr. accessStore l (Memory st') = Some (MPointer ptr)
                    \<and> LSubPrefL2 ptr (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> MCon (MTArray x t) (Memory st') ptr "
      using MCondest2 accessL mInStd
      by (simp add: LSubPrefL2_def )


    have notTopSublocs_inv:"\<forall>dloc1 x11 x12 stl1 i. \<not> LSubPrefL2 dloc1 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> TypedMemSubPrefPtrs (Memory st') x11 x12 stl1 dloc1
                          \<longrightarrow> TypedMemSubPrefPtrs (Memory st) x11 x12 stl1 dloc1"
    proof intros
      fix dloc1 x11 x12 stl1
      assume "\<not> LSubPrefL2 dloc1 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> TypedMemSubPrefPtrs (Memory st') x11 x12 stl1 dloc1"
      then have asm3:"\<not> LSubPrefL2 dloc1 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))"
          and asm4:"TypedMemSubPrefPtrs (Memory st') x11 x12 stl1 dloc1" by simp+
      show "TypedMemSubPrefPtrs (Memory st) x11 x12 stl1 dloc1 " using asm3 asm4
      proof(induction x12 arbitrary:x11 stl1)
        case (MTArray x1 x12)
        obtain i'' ptr where ptrDef:"i''<x11 \<and> accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st') = Some (MPointer ptr)
                  \<and> (ptr = dloc1 \<or> TypedMemSubPrefPtrs (Memory st') x1 x12 ptr dloc1)"
          using MTArray.prems(2) unfolding TypedMemSubPrefPtrs.simps by auto
        then have notl:"(hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) \<noteq> l" using MTArray.prems(1)
          by (metis BT3 LSubPrefL2_def memoryvalue.inject(2) accessL mInStd option.inject)
        have notSub:"\<not>LSubPrefL2 (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))"
          using SubPtrs_top asm3 ptrDef selfPoint2 by blast
        have sameAccess:"accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st') = accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st)"
          using notl notSub nonLocChanged2 by auto
        then show ?case
        proof(cases "ptr = dloc1")
          case True
          then show ?thesis using sameAccess ptrDef by force
        next
          case False
          then show ?thesis using MTArray.IH sameAccess ptrDef
            by (metis asm3 TypedMemSubPrefPtrs.simps(2))
        qed
      next
        case (MTValue x)
        then show ?case by simp
      qed
    qed

    have subPrefM:"subPrefixStructuralConsistency (m)"
      using cpm2m_subPrefixPersist[OF _ _ _ sameTypeAccess _ sameTypeAccess2 tps MCondest]
        \<open>accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (snd (allocate (Memory st))) = None\<close> allocateSame
        nonLocChanged a32 tps2 selfPoint 2(1) unfolding TypeSafe_def by metis


    show ?thesis unfolding TypeSafe_def StateInvariant_def
    proof intros
      show "AddressTypes (Accounts st')" using 2(1) 7 unfolding TypeSafe_def by simp
    next
      show "unique_locations (Denvalue env)" using 2(1) unfolding TypeSafe_def by simp
    next
      have a0:" compPointers (Stack st) (Denvalue env)" using 2(1) unfolding TypeSafe_def by blast
      then show "compPointers (Stack st') (Denvalue env)" using sameStack sameStorage by simp
    next
      show "safeContract (Accounts st') (Storage st')" using sameStorage 7 using 2(1) unfolding TypeSafe_def safeContract_def by auto
    next
      show "balanceTypes (Accounts st')" using 7 using 2(1) unfolding TypeSafe_def by simp
    next
      have "envAddressesWellFormed env" using 2(1) unfolding TypeSafe_def by simp
      then show "addressFormat (Address env)" and "addressFormat (Sender env)" by simp+
    next
      show "svalueTypes (Svalue env)" using 2(1) unfolding TypeSafe_def by simp
    next
      have *:"((\<forall>tloc loc. Toploc (Stack st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Stack st) = None) \<and>
            (\<forall>loc y. accessStore loc (Stack st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Stack st). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))) "
        using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by simp
      have **:"Toploc (Stack st) = Toploc (Stack st')" using 7 unfolding updateStore_def by auto
      show "lessThanTopLocs (Stack st')" unfolding lessThanTopLocs_def
      proof intros

        fix tloc loc
        assume h1:"Toploc (Stack st') \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
        then have "Toploc (Stack st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)" using ** by simp
        then show "accessStore loc (Stack st') = None" using *
          by (simp add: sameStack)
      next
        fix loc y
        assume h1:" accessStore loc (Stack st') = Some y"
        then show "\<exists>tloc<Toploc (Stack st'). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)" using ** *
          by (metis sameStack)
      qed
    next
      show "lessThanTopLocs cd" using 2(1) unfolding TypeSafe_def by simp
    next
      have a10:"Toploc (snd (allocate (Memory st))) = Toploc m"
        using cpm2mTopLocSame[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd "(snd (allocate (Memory st)))" x m] 7(4) mInStd unfolding cpm2m_def by fastforce
      then have a12:"Toploc m = Toploc m'" using 7(5) unfolding updateStore_def by auto
      have a15:"lessThanTopLocs (Memory st)" using 2 unfolding TypeSafe_def by simp
      have tloc:"Toploc (Memory st) < Toploc (snd (allocate (Memory st)))" unfolding allocate_def by simp
      show "lessThanTopLocs (Memory st')" unfolding lessThanTopLocs_def
      proof intros
        fix tloc loc
        assume b10: "Toploc (Memory st') \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
        then have b20:"Toploc (Memory st) \<le> tloc" using a10 tloc a12
          using mInStd by force

        then show "accessStore loc (Memory st') = None "
          by (metis (no_types, lifting) LSubPrefL2_def MemLSubPrefTransitive NonChangeM'm \<open>\<exists>x. accessStore l (Memory st) =
              Some x\<close> a10 a12 allocateSame antisym_conv2 b10 hash_inequality
              hash_suffixes_associative hashesIntSame limitSt mInStd nonLocChanged option.discI order_less_le_trans tloc)
      next
        fix loc y
        assume "accessStore loc (Memory st') = Some y "
        then show "\<exists>tloc<Toploc (Memory st'). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
          by (metis NonChangeM'm \<open>\<exists>x. accessStore l (Memory st) = Some x\<close> a10 a12 allocateSameAccess limitSt1 mInStd nonLocChanged order_less_trans tloc)
      qed
    next
      show " typeCompat (Denvalue env) (Stack st') (Memory st') (Storage st' (Address env)) cd"
        unfolding typeCompat_def
      proof intros
        fix tLook lLook
        assume inDen:" (tLook, lLook) |\<in>| fmran (Denvalue env)"
        show " denvalueCon (Stack st') (Memory st') (Storage st' (Address env)) cd tLook lLook"
        proof(cases lLook)
          case (Stackloc x1)
          then obtain a where adef:"accessStore x1 (Stack st') = Some a" using inDen Stackloc 2(1) unfolding TypeSafe_def typeCompat_def using sameStack nonChangedStack by fastforce
          then show ?thesis
          proof(cases "a")
            case (KValue x1)
            then show ?thesis using Stackloc adef inDen Stackloc 2(1) sameStack nonChangedStack unfolding TypeSafe_def typeCompat_def
              by (metis (no_types, lifting) denvalue.simps(5) Option.option.simps(5) stackvalue.simps(17) )
          next
            case (KCDptr x2)
            then show ?thesis using Stackloc adef inDen Stackloc 2(1) sameStack nonChangedStack unfolding TypeSafe_def typeCompat_def
              by (metis (no_types, lifting) denvalue.simps(5) Option.option.simps(5) stackvalue.simps(18))
          next
            case (KMemptr x3)
            then have "\<exists>struct. tLook = type.Memory struct" using Stackloc adef inDen Stackloc 2(1) KMemptr sameStack unfolding TypeSafe_def typeCompat_def by (cases tLook;force+)
            then obtain struct where structdef:"tLook = type.Memory struct" by blast

            then have mcOld:"MCon struct (Memory st) x3" using 2(1) unfolding TypeSafe_def typeCompat_def
              using Stackloc adef inDen KMemptr sameStack by (auto split:type.splits denvalue.splits stackvalue.splits option.splits)
            then have mcM:"MCon struct m x3" using PreExistMconNotChangeByToploc limitSt limitSt1 nonLocChanged22
              by auto
            have structss:"(case struct of
     MTArray len arr \<Rightarrow>
       (\<forall>i<len. accessTypeStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr)
     | MTValue val \<Rightarrow> accessTypeStore x3 (Memory st) = Some (MTValue val))"
              using 2(1) inDen KMemptr Stackloc structdef adef 7(6)
              unfolding TypeSafe_def denvalueTypeCorrectness_def by simp
            then have structss:"(case struct of
     MTArray len arr \<Rightarrow>
       (\<forall>i<len. accessTypeStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr)
     | MTValue val \<Rightarrow> accessTypeStore x3 (Memory st) = Some (MTValue val))"
              by (metis (no_types, lifting))
            have nonLocChanged_TypedSafe:"\<forall>loc. \<not> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))
                                        \<longrightarrow> accessTypeStore loc m = accessTypeStore loc (Memory st)"
            proof -
              have "\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<or> locs =
                  (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow> accessTypeStore locs (snd (allocate (Memory st)))
                  = accessTypeStore locs m"
                using 7(4,5,6) cpm2mSingleChange_Typed[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd " (snd (allocate (Memory st)))" x m ]
                  cpm2m_def[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" x t cd " (snd (allocate (Memory st)))" ] by simp
              then show "\<forall>loc. \<not> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow> accessTypeStore loc m = accessTypeStore loc (Memory st)"
                using allocateTypeSameAccess mInStd by metis
            qed

            then have "accessTypeStore x3 (Memory st) = accessTypeStore x3 m"
              using limitSt limitSt1 mcOld
              by (metis AllPtrsNotTop_MCon lessThanTopLocs_def nat_le_linear)
            moreover have eq2:"\<forall>i::nat. accessTypeStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = accessTypeStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (m)"
              using nonLocChanged_TypedSafe limitSt limitSt1 mcOld AllPtrsNotTop_MCon lessThanTopLocs_def
              by (metis MemLSubPrefL2_specific_imps_general nat_le_linear)
            ultimately have structss:"(case struct of
     MTArray len arr \<Rightarrow>
       (\<forall>i<len. accessTypeStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some arr)
     | MTValue val \<Rightarrow> accessTypeStore x3 m = Some (MTValue val))" using structss by presburger

            have "accessTypeStore l (Memory st) = Some (MTArray x t)"
              using lInfo 7 nonLocChanged by auto
            then have accl:"accessTypeStore l (m) = Some (MTArray x t)"
              using nonLocChanged_TypedSafe
              using l_not_toploc_orSub by auto
            have "MCon struct (Memory st') x3"
              using cpm2m_singleLChange[OF mcM structss _ _ _ MCondest2 subPrefM] 7(5) mInStd
              by (metis NonChangeM'm accl lOld2)

            then show ?thesis using structdef KMemptr Stackloc adef inDen Stackloc 2(1) unfolding TypeSafe_def typeCompat_def by simp

          next
            case (KStoptr x4)
            then show ?thesis using Stackloc adef sameStorage inDen Stackloc KStoptr 2(1) nonChangedStack sameStack unfolding TypeSafe_def typeCompat_def
                apply(cases tLook) by fastforce+
          qed

          next
          case (Storeloc x2)
          then show ?thesis using sameStorage inDen 2(1) unfolding TypeSafe_def typeCompat_def by (cases tLook; force)
        qed
      qed
      then have "typeCompat (Denvalue env) (Stack st) (Memory st') (Storage st' (Address env)) cd" using sameStack by simp
      next
      have "Accounts st'= Accounts st" using 7 by auto
      then show "fullyInitialised env (Accounts st') (Stack st')" using 2(3) 7 unfolding fullyInitialised_def by auto
      next
      have tloc:"Toploc (Memory st) < Toploc (snd (allocate (Memory st)))" unfolding allocate_def by simp
      have topLocEq:"Toploc (snd (allocate (Memory st))) = Toploc m"
          using cpm2mTopLocSame[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd "(snd (allocate (Memory st)))" x m] 7(4) mInStd unfolding cpm2m_def by fastforce
      then have topmm':"Toploc m = Toploc m'" using 7(5) unfolding updateStore_def by auto
      then have topm'st':"Toploc m' = Toploc (Memory st')" using mInStd by blast

      then have "{l. Toploc (Memory st) \<le> l \<and> l < Suc (Toploc (Memory st))} = {(Toploc (Memory st))}" by auto
      then have "{l. Toploc (Memory st) \<le> l \<and> l < (Toploc m)} = {(Toploc (Memory st))}" using topLocEq mInStd unfolding allocate_def by auto
      then have topLocSet:"{(ShowL\<^sub>n\<^sub>a\<^sub>t l) |l. Toploc (Memory st) \<le> l \<and> l < Toploc m} = {ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))}"
          by (simp add: setcompr_eq_image)
      have "\<forall>l. l \<in> WrittenMem_between (Memory st) (m) \<longrightarrow> TypedMemSubPref l (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x t) "
          using WrittenMem_between_def mInStd a30 selfPoint a32 by blast
      then have "\<forall>l''. l'' \<in> WrittenMem_between (Memory st) (m') \<longrightarrow> TypedMemSubPref l'' (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x t) \<or> l'' = l"
          using NonChangeM'm WrittenMem_between_def by fastforce
      then have cc0:"\<forall>l''. l'' \<in> WrittenMem_between (Memory st) (Memory st') \<longrightarrow> TypedMemSubPref
          l'' (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x t) \<or> l'' = l" using mInStd by simp
      moreover have aloccated:"\<forall>x'. x'\<in> (AllocatedMem_between (Memory st) m) \<longleftrightarrow> TypedMemSubPref x'
          (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x t) \<or> x' = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory
          st)))"
      proof intros
        fix x'
        show "(x' \<in> AllocatedMem_between (Memory st) m) = (TypedMemSubPref x' (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))
            (MTArray x t) \<or> x' = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))))"
        proof
          assume " x' \<in> AllocatedMem_between (Memory st) m"
          then have "x' \<in> {(ShowL\<^sub>n\<^sub>a\<^sub>t l) |l. Toploc (Memory st) \<le> l \<and> l < Toploc m} \<union> fset (fmdom (Mapping m) |-| fmdom (Mapping (Memory st)))"
              unfolding AllocatedMem_between_def by simp
          then have "x' \<in> ({(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))} \<union> fset (fmdom (Mapping m) |-| fmdom (Mapping (Memory st))))"
              using topLocSet by simp
          then show "TypedMemSubPref x' (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x t) \<or> x' = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))"
              using a30 accessStore_def allocateSame fminus_iff fmlookup_dom_iff
              by (metis Un_iff empty_iff insert_iff)
          next
          assume *:"TypedMemSubPref x' (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x t) \<or> x' = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))"

          then show "x' \<in> AllocatedMem_between (Memory st) m"
          proof(cases "x' = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))")
            case True
            then show ?thesis unfolding AllocatedMem_between_def using topLocSet by simp
            next
            case False
            then have "accessStore x' (Memory st) = None" using limitSt typedPrefix_imp_SubPref * by blast

            moreover have "\<exists>v. accessStore x' m = Some v" using * MCondest selfPoint MCon_imps_TypedMemSubPref_Some False by blast

            ultimately have "x' \<in> fset (fmdom (Mapping m) |-| fmdom (Mapping (Memory st)))" using a30
                by (simp add: accessStore_def fmlookup_dom_iff)
            then show ?thesis using AllocatedMem_between_def by auto
          qed
        qed
      qed
      moreover have "accessStore l m = accessStore l (Memory st)"
          using l_not_toploc_orSub nonLocChanged22 by fastforce
      moreover obtain vv where vvdef:"accessStore l m = Some vv" using calculation lIs by auto
      moreover have lIn22:"l |\<in>| fmdom (Mapping m)" using fmdomI calculation(4) accessStore_def by metis
      moreover have "accessStore l m' = Some (MPointer (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))))" using fmdomI 7(5) by auto
      moreover have "l |\<in>| fmdom (Mapping m')" using calculation(6) fmdomI
          by (metis accessStore_def)
      next
      show "denvalueTypeCorrectness env (Stack st') (Memory st')"
          unfolding denvalueTypeCorrectness_def
      proof intros
        fix t2 l2 ptr_loc
        assume *:"(type.Memory t2, Stackloc l2) |\<in>| fmran (Denvalue env) \<and> accessStore l2 (Stack st') = Some (KMemptr ptr_loc)"
        have sameACC:"accessStore l2 (Stack st') = accessStore l2 (Stack st)"
            using nonChangedStack * 7(5,6) unfolding accessStore_def updateStore_def by simp


        show "case t2 of MTArray len arr \<Rightarrow> (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr)
                         | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st') = Some (MTValue val)"
        proof(cases t2)
          case (MTArray x11 x12)

          have old':"(\<forall>i<x11. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some x12)"
              using sameACC 2(1) * unfolding TypeSafe_def denvalueTypeCorrectness_def using MTArray by force

          have conc0:"(\<forall>i<x11. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some x12)"
          proof -
            have o:"\<forall>i<x11. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some x12" using old' by blast
            then have "\<forall>i<x11. \<exists>v. accessStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some v"
                using 2(1) unfolding TypeSafe_def SomeValSomeTyp_def by auto
            then have "\<forall>i<x11. \<not> LSubPrefL2 (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))"
                using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by fastforce
            then show ?thesis using nonLocChanged_TypedSafe o by simp
          qed

          then show ?thesis using MTArray by simp
          next
          case (MTValue x2)
          then show ?thesis using sameACC 2(1) * unfolding TypeSafe_def denvalueTypeCorrectness_def
              by (metis (no_types, lifting) mtypes.simps(6) nonLocChanged_TypedSafe stackDenvalLimits)
        qed
      qed
      next
      show "subPrefixStructuralConsistency (Memory st')"
          unfolding subPrefixStructuralConsistency_def
      proof intros
        fix locs tp
        assume in1:" accessTypeStore locs (Memory st') = Some tp "
        have sameTy:"\<forall>locs. accessTypeStore locs m = accessTypeStore locs (Memory st') "
            using mInStd by (metis NonChangeM'mT)
        then have in2:"accessTypeStore locs m = Some tp " using in1 by simp
        show "case accessStore locs (Memory st') of None \<Rightarrow> False
              | Some (MValue v) \<Rightarrow> \<exists>val. MCon tp (Memory st') locs \<and> tp = MTValue val \<and> accessTypeStore locs (Memory st') = Some tp
              | Some (MPointer p) \<Rightarrow>
                 \<exists>len arr.
                    MCon tp (Memory st') p \<and>
                    tp = MTArray len arr \<and>
                    (\<forall>i<len. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr)"
        proof(cases "locs = l")
          case True
          have "accessTypeStore l (Memory st) = Some (MTArray x t)"
              using lInfo 7 nonLocChanged by auto
          then have accl:"accessTypeStore l (m) = Some (MTArray x t)"
              using nonLocChanged_TypedSafe l_not_toploc_orSub
              using sameTypeAccess by auto
          then have tpDef:"tp = MTArray x t"
              using sameTy True in1 by simp
          then have ptr:"accessStore locs (Memory st') = Some (MPointer (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))))"
              using mInStd True by (metis accessL)
          have sameAccm:"accessStore l m = accessStore l (Memory st)"
              using l_not_toploc_orSub nonLocChanged22 by fastforce
          moreover have " MCon tp (Memory st') (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))"
              using MCondest2 tpDef by blast
          moreover have "(\<forall>i<x. accessTypeStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some t)"
              using tpDef ptr subPrefM sameAccm accl unfolding subPrefixStructuralConsistency_def
              using sameTy tps2 by presburger
          moreover have "
         (\<forall>v. accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (Memory st') = Some (MPointer v)
                \<longrightarrow> accessTypeStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (Memory st') = Some (MTArray x t))"
              using LSubPrefL2_def selfPoint2 by blast
          ultimately show ?thesis using True tpDef ptr by auto
          next
          case False
          then have sameACC:"accessStore locs m = accessStore locs (Memory st')"
              using mInStd NonChangeM'm by simp
          then have in3:"(case accessStore locs m of None \<Rightarrow> False | Some (MValue v) \<Rightarrow> \<exists>val. MCon tp m locs
              \<and> tp = MTValue val \<and> accessTypeStore locs m = Some tp
      | Some (MPointer p) \<Rightarrow>
          \<exists>len arr.
             MCon tp m p \<and>
             tp = MTArray len arr \<and>
             (\<forall>i<len. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some arr) )"
              using subPrefM in2 unfolding subPrefixStructuralConsistency_def by blast
          then show ?thesis
          proof(cases "accessStore locs m")
            case None
            then show ?thesis using in3 sameACC by simp
            next
            case (Some a)
            then show ?thesis
            proof(cases a)
              case (MValue x1)
              then obtain val where " MCon tp m locs \<and> tp = MTValue val \<and> accessTypeStore locs m = Some tp"
                  using in3 Some by auto
              moreover have "MCon tp (Memory st') locs" using sameACC calculation by auto
              ultimately show ?thesis using sameACC Some MValue sameTy
                  by (auto split:option.splits)
              next
              case (MPointer x2)
              have "accessTypeStore l (Memory st) = Some (MTArray x t)"
                  using lInfo 7 nonLocChanged by auto
              then have accl:"accessTypeStore l (m) = Some (MTArray x t)"
                  using nonLocChanged_TypedSafe l_not_toploc_orSub
                  using sameTypeAccess by auto
              then obtain len arr where s:"MCon tp m x2 \<and> tp = MTArray len arr \<and>
                         (\<forall>i<len. accessTypeStore (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some arr)"
                  using Some in3 MPointer by auto
              then have mcM:"MCon tp m x2" by auto
              then have "MCon tp (Memory st') x2"
                  using cpm2m_singleLChange[OF mcM _ _ _ _ MCondest2 subPrefM, of l]
                    7(5) accl mInStd s NonChangeM'm accessL lOld2
                  by simp
              moreover have "(\<forall>i<len. accessTypeStore (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr)"
                  using s sameTy by simp

              ultimately show ?thesis using Some MPointer sameACC sameTy s
                  by (auto split:option.splits)
            qed
          qed
        qed
      qed

      next
      have old:"(\<forall>locs. (\<exists>t. accessStore locs (Memory st) = Some t) = (\<exists>tt. accessTypeStore locs (Memory st) = Some tt))"
          using 2(1) unfolding TypeSafe_def SomeValSomeTyp_def by blast
      have somesome:"\<forall>destl'. TypedMemSubPref destl' (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x t)
            \<longrightarrow> (\<exists>t. accessStore destl' m = Some t) = (\<exists>tt. accessTypeStore destl' m = Some tt)"
          using 7(4) unfolding cpm2m_def using cpm2m_TypeCompChange_somesome[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd "(snd (allocate (Memory st)))" x m]
          by simp
      have a30T:"\<forall>locs. \<not> TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x t)
                \<longrightarrow> accessTypeStore locs (Memory st) = accessTypeStore locs m"
          using 7(4) unfolding cpm2m_def using cpm2mSingleChange_typedPref_typed[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd " (snd (allocate (Memory st)))" x m ]
            mInStd allocateTypeSameAccess by metis
      show "SomeValSomeTyp (Memory st')"unfolding SomeValSomeTyp_def
      proof intros
        fix locs
        show "(\<exists>t. accessStore locs (Memory st') = Some t) = (\<exists>tt. accessTypeStore locs (Memory st') = Some tt) "
        proof(cases "TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x t)")
          case True
          then have ss:"(\<exists>t. accessStore locs m = Some t) = (\<exists>tt. accessTypeStore locs m = Some tt)"
              using somesome by simp
          then show ?thesis
          proof(cases "locs = l")
            case True
            then show ?thesis using lInfo NonChangeM'mT accessL mInStd ss
                using lIs l_not_toploc_orSub nonLocChanged22 by auto
            next
            case False
            then show ?thesis using ss NonChangeM'mT NonChangeM'm mInStd by simp
          qed
          next
          case False
          then have acc1:"accessStore locs (Memory st) = accessStore locs m"
              using a30 mInStd allocateSameAccess by metis
          have acc2:"accessTypeStore locs (Memory st) = accessTypeStore locs (Memory st')"
              using a30T False mInStd NonChangeM'mT by simp
          show ?thesis
          proof(cases "locs = l")
            case True
            then show ?thesis using lInfo acc2 accessL mInStd by force
            next
            case False
            then have "accessStore locs m = accessStore locs (Memory st')"
                using mInStd NonChangeM'm by auto
            then show ?thesis using old acc1 acc2 by metis
          qed
        qed
      qed
      next
      fix locs t2
      assume acc1:"accessTypeStore locs (Memory st) = Some t2"
      then have someSome:"\<exists>v. accessStore locs (Memory st) = Some v"
          using 2(1) unfolding TypeSafe_def SomeValSomeTyp_def by simp
      have a30T:"\<forall>locs. \<not> TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x t)
                \<longrightarrow> accessTypeStore locs (Memory st) = accessTypeStore locs m"
          using 7(4) unfolding cpm2m_def using cpm2mSingleChange_typedPref_typed[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd " (snd (allocate (Memory st)))" x m ]
            mInStd allocateTypeSameAccess by metis

      show "accessTypeStore locs (Memory st') = Some t2"
      proof(cases "TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x t)")
        case True
        then show ?thesis
        proof(cases "locs = l")
          case True
          then show ?thesis using l_not_toploc_orSub
              by (metis NonChangeM'mT a30T acc1 mInStd typedPrefix_imp_SubPref)
          next
          case False
          then show ?thesis using NonChangeM'mT a30T typedPrefix_imp_SubPref acc1 NonChangeM'm mInStd someSome
              by (metis less_or_eq_imp_le limitSt option.distinct(1))
        qed
        next
        case False
        have acc2:"accessTypeStore locs (Memory st) = accessTypeStore locs (Memory st')"
            using a30T False mInStd NonChangeM'mT by simp
        show ?thesis
        proof(cases "locs = l")
          case True
          then show ?thesis using lInfo acc2 accessL mInStd acc1 by argo
          next
          case False
          then have "accessStore locs m = accessStore locs (Memory st')"
              using mInStd NonChangeM'm by auto
          then show ?thesis using acc1 acc2 by metis
        qed
      qed
      next
      show "\<And>locs v. accessStore locs (Memory st) = Some (MPointer v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MPointer v')"
          by (metis accessL le_refl limitSt mInStd nonLocChanged2 option.distinct(1))
      next
      show "\<And>locs v. accessStore locs (Memory st) = Some (MValue v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MValue v')"
          by (metis memoryvalue.distinct(1) lOld le_refl limitSt nonLocChanged2 not_None_eq option.inject)
      next
      fix i loc
      assume a1:"i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)"
          and a2:"accessStore loc (Memory st) = None"
      then have "loc \<noteq> l" using lOld by auto
      moreover have "\<not> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" using a1
          by (metis (no_types, opaque_lifting) LSubPrefL2_def MemLSubPrefTransitive hash_flatten_right hash_inequality hashesIntSame nless_le)
      ultimately show " accessStore loc (Memory st') = None" using a2 nonLocChanged2 by simp
      next
      have tloc:"Toploc (Memory st) < Toploc (snd (allocate (Memory st)))" unfolding allocate_def by simp
      moreover have topLocEq:"Toploc (snd (allocate (Memory st))) = Toploc m"
          using cpm2mTopLocSame[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t cd "(snd (allocate (Memory st)))" x m] 7(4) mInStd unfolding cpm2m_def by fastforce
      moreover have topmm':"Toploc m = Toploc m'" using 7(5) unfolding updateStore_def by auto
      moreover have topm'st':"Toploc m' = Toploc (Memory st')" using mInStd by blast
      ultimately show "Toploc (Memory st) \<le> Toploc (Memory st')" by simp
    qed
  qed
qed

text \<open>Assignment case 8: a memory array assigned to a memory variable on the stack: the stack now points to the same array.\<close>

lemma TypeSafe_Assign_8:
  assumes "TypeSafe env (Accounts st) (Stack st) (Memory st) (Storage st) cd"
    and "stmt (ASSIGN lv ex) env cd st = Normal ((), st')"
    and "fullyInitialised env (Accounts st) (Stack st)"
    and "expr ex env cd (st\<lparr>state.Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>) (state.Gas st - costs (ASSIGN lv
        ex) env cd st) = Normal ((KMemptr p, type.Memory (MTArray x t)), g)"
    and "lexp lv env cd (st\<lparr>state.Gas := g\<rparr>) g = Normal((LStackloc l, type.Memory t'),g')"
    and "t' = MTArray x t"
    and "st' = st\<lparr>state.Gas := g', Stack := updateStore l (KMemptr p) (Stack st)\<rparr>"
  shows "StateInvariant env st st' cd"
proof -
  let ?case = "StateInvariant env st st' cd"
  note 2 = assms(1-3)
  note 8 = assms(4-7)
  then have stackChanged:"\<forall>l'. l' \<noteq> l \<longrightarrow> accessStore l' (Stack st) = accessStore l' (Stack st')" unfolding updateStore_def accessStore_def by simp
  have t'InDen:"(type.Memory t', Stackloc l) |\<in>| fmran (Denvalue env)" using lexpStackloc_imps_inDen[OF 8(2)] by blast
  then have lDen:"\<forall>t'. (t', Stackloc l) |\<in>| fmran (Denvalue env) \<longrightarrow> t'= (type.Memory (MTArray x t))" using 8 2(1) unfolding TypeSafe_def unique_locations_def by auto

  have pOrigin:"MCon (MTArray x t) (Memory (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)) (extractValueType (KMemptr p)) \<and>
      (\<exists>xx. KMemptr p = KMemptr xx) \<and>
      (\<exists>stloc tp'' pa.
          (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue env) \<and>
          accessStore stloc (Stack (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)) = Some (KMemptr pa) \<and>
          (tp'' = (MTArray x t) \<and> KMemptr p = KMemptr pa \<or>
           (\<exists>len arr.
               extractValueType (KMemptr p) \<noteq> pa \<and>
               tp'' = MTArray len arr \<and> CompMemType (Memory (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)) len arr (MTArray x t) pa (extractValueType (KMemptr p)))))"
    using 2(1) 8(1) 2(3) using
      exprTypeconInduct(3)[of ex env cd "(st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)" "(state.Gas st - costs
          (ASSIGN lv ex) env cd st)" "KMemptr p" "type.Memory (MTArray x t)" g]
    by (auto split:type.splits if_splits )
  then obtain pParent pParentT pParentPtr where
    pOrigin:"MCon (MTArray x t) (Memory (st)) (extractValueType (KMemptr p)) \<and>(type.Memory pParentT, Stackloc pParent) |\<in>| fmran (Denvalue env) \<and>
          accessStore pParent (Stack (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)) = Some (KMemptr pParentPtr) \<and>
          (pParentT = (MTArray x t) \<and> KMemptr p = KMemptr pParentPtr \<or>
           (\<exists>len arr.
               extractValueType (KMemptr p) \<noteq> pParentPtr \<and>
               pParentT = MTArray len arr \<and> CompMemType (Memory (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd
                   st\<rparr>)) len arr (MTArray x t) pParentPtr (extractValueType (KMemptr p))))"
    using pOrigin by force
  have pMCon:"MCon (MTArray x t) (Memory st) p" using pOrigin by force

  have storageSame:"(Storage st' (Address env)) = (Storage st (Address env))" using 8 by simp
  have memorySame:"Memory st = Memory st'" using 8 by simp
  show ?thesis unfolding TypeSafe_def StateInvariant_def
  proof (intros)
    show tcN:"typeCompat (Denvalue env) (Stack st') (Memory st') (Storage st' (Address env)) cd"
      unfolding typeCompat_def
    proof(intros)
      fix t l' assume a10:"(t, l') |\<in>| fmran (Denvalue env)"
      show "denvalueCon (Stack st') (Memory st') (Storage st' (Address env)) cd t l'"
      proof (split denvalue.split, intros)
        fix loc assume a20:"l' = Stackloc loc"
        show "(case accessStore loc (Stack st') of None \<Rightarrow> False
              | Some (KValue val) \<Rightarrow> (case t of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
              | Some (KCDptr stloc) \<Rightarrow> (case t of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
              | Some (KMemptr stloc) \<Rightarrow> (case t of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
              | Some (KStoptr stloc) \<Rightarrow> (case t of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address env)) | _ \<Rightarrow> False))"
        proof (cases "loc = l")
          case False
          show ?thesis
          proof (split option.split, intros)
            assume a30:"accessStore loc (Stack st') = None"
            then have "accessStore loc (Stack st) = None" using 8(4) False by (simp add:stackSingleUpdate)
            then show False using a30 a20 a10 assms TypeSafe_def False 2(1)
              by (metis option.distinct(1) typeSafeLocExists)
          next
            fix x2 assume a30:"accessStore loc (Stack st') = Some x2"
            then have a40:"accessStore loc (Stack st) = Some x2" using 8(4) False by (simp add:stackSingleUpdate)
            then have a50:"(Memory st) = (Memory st')" using 8(4) by simp
            then have a60:"(Storage st) = (Storage st')" using 8(4) by simp
            show "case x2 of KValue val \<Rightarrow> (case t of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
                  | KCDptr stloc \<Rightarrow> (case t of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
                  | KMemptr stloc \<Rightarrow> (case t of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
                  | KStoptr stloc \<Rightarrow> (case t of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address env)) | _ \<Rightarrow> False)"
              using a10 a20 a30 a40 a50 a60 2(1) unfolding TypeSafe_def typeCompat_def by (cases x2; cases t; force)
          qed
        next
          case sameLoc:True
          show ?thesis
          proof (split option.split, intros)
            assume a30:"accessStore loc (Stack st') = None"
            then show False using a20 a10 assms(1) sameLoc 8(4) notNoneUpdate[of st' g' loc "(KMemptr p)" ] by simp
          next
            fix x2 assume a30:"accessStore loc (Stack st') = Some x2"
            then have x2IsP:"x2 = KMemptr p" using 8 sameLoc by auto
            show "case x2 of KValue val \<Rightarrow> (case t of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
                  | KCDptr stloc \<Rightarrow> (case t of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
                  | KMemptr stloc \<Rightarrow> (case t of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
                  | KStoptr stloc \<Rightarrow> (case t of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address env)) | _ \<Rightarrow> False)"
            proof(cases "x2")
              case (KValue x1)

              then show ?thesis using x2IsP by auto
            next
              case (KCDptr x2)
              then show ?thesis using x2IsP by (simp add:sameLoc)
            next
              case (KMemptr x3)
              then show ?thesis
                using a10 a20 lDen memorySame pMCon sameLoc x2IsP by fastforce
            next
              case (KStoptr x4)
              then show ?thesis using x2IsP by (simp add:sameLoc)
            qed
          qed
        qed
      next
        fix x2 assume a20:"l' = Storeloc x2"
        then have "(Storage st' (Address env)) = (Storage st (Address env))" using 8(4) by simp
        then show "case t of type.Storage typ \<Rightarrow> SCon typ x2 (Storage st' (Address env)) | _ \<Rightarrow> False"
          using a10 a20 2(1) unfolding TypeSafe_def typeCompat_def by (cases t; force)
      qed
    qed
    have "typeCompat (Denvalue env) (Stack st) (Memory st') (Storage st' (Address env)) cd"
      unfolding typeCompat_def
    proof(intros)
      fix t l' assume a10:"(t, l') |\<in>| fmran (Denvalue env)"
      show "denvalueCon (Stack st) (Memory st') (Storage st' (Address env)) cd t l'"
      proof(cases l')
        case (Stackloc x1)
        then show ?thesis
        proof(cases "x1= l")
          case True
          then obtain t''' where tdef:"t = type.Memory t'''" using lDen a10 Stackloc 2(1) by blast
          then have x2IsP:"\<exists>p. accessStore x1 (Stack st) = Some (KMemptr p)"
          proof(cases "accessStore x1 (Stack st)")
            case None
            then show ?thesis using 8 True 2(1) a10 Stackloc unfolding TypeSafe_def typeCompat_def by force
          next
            case (Some a)
            then show ?thesis using tdef 8 True 2(1) a10 Stackloc unfolding TypeSafe_def typeCompat_def
              by (cases a, force+ )
          qed
          then show ?thesis using a10 Stackloc lDen memorySame pMCon True tdef x2IsP 2(1) unfolding TypeSafe_def typeCompat_def by force
        next
          case False
          then have "accessStore x1 (Stack st) = accessStore x1 (Stack st')"
            using stackChanged by auto
          then show ?thesis using tcN a10 Stackloc unfolding typeCompat_def by force
        qed
      next
        case (Storeloc x2)
        then show ?thesis using tcN a10 unfolding typeCompat_def by force
      qed
    qed
  next
    show "unique_locations (Denvalue env)" using 2(1) typeSafeUnique by auto
  next
    have "(Accounts st) = Accounts(st')" using 8 by simp
    then show "balanceTypes (Accounts st')" using balanceTypes_def balanceTypes_def 2(1) typeSafeAccounts by simp
  next
    have a0:"compPointers (Stack st) (Denvalue env)" using 2(1) storageSame unfolding TypeSafe_def by simp
    show " compPointers (Stack st') (Denvalue env)" unfolding compPointers_def
    proof(intros)
      fix tp1 tp2 l1 l22 l1' l2' stl1 stl2
      assume a1:"(type.Storage tp1, l1) |\<in>| fmran (Denvalue env) \<and>
     (type.Storage tp2, l22) |\<in>| fmran (Denvalue env) \<and>
     (l1 = Stackloc l1' \<and> accessStore l1' (Stack st') = Some (KStoptr stl1) \<or> l1 = Storeloc stl1) \<and>
     (l22 = Stackloc l2' \<and> accessStore l2' (Stack st') = Some (KStoptr stl2) \<or> l22 = Storeloc stl2)"
      have a2:"(\<forall>x y. x |\<in>| fmran (Denvalue env) \<and> y |\<in>| fmran (Denvalue env) \<and> snd x = snd y \<longrightarrow> x = y)"
        using 2(1) unfolding TypeSafe_def unique_locations_def by simp

      have a3:"l1 \<noteq> Stackloc l \<and> l22 \<noteq> Stackloc l" using a2 t'InDen a1 by auto

      then show "if TypedStoSubpref stl2 stl1 tp1 then CompStoType tp1 tp2 stl1 stl2 else if TypedStoSubpref stl1 stl2 tp2 then CompStoType tp2 tp1 stl2 stl1 else True"
      proof(cases "l1 = Storeloc stl1")
        case t1:True
        then show ?thesis
        proof(cases "l22 = Storeloc stl2")
          case True
          then show ?thesis using t1 a0 a1 unfolding compPointers_def by blast
        next
          case False
          then have " accessStore l2' (Stack st') = accessStore l2' (Stack st)" using stackChanged a3 a1 by simp
          then show ?thesis using a0 a1 t1 unfolding compPointers_def by metis
        qed
      next
        case f1:False
        then have l1Same:"accessStore l1' (Stack st') = accessStore l1' (Stack st)"
          using stackChanged a3 a1 by simp
        then show ?thesis
        proof(cases "l22 = Storeloc stl2")
          case True
          then show ?thesis using f1 a0 a1 l1Same unfolding compPointers_def by metis
        next
          case False
          then have "accessStore l2' (Stack st') = accessStore l2' (Stack st)"
            using stackChanged a3 a1 by simp
          then show ?thesis using a0 a1 l1Same unfolding compPointers_def by metis
        qed
      qed

    qed
  next
    show "svalueTypes (Svalue env)" using svalueTypes_def typeSafeSvalue 2(1) by simp
  next
    have "(Storage st') = (Storage st)" using 8(4) by simp
    then show "safeContract (Accounts st') (Storage st')" using 2(1) 8 unfolding safeContract_def TypeSafe_def by auto
  next
    have a10:"Toploc (Stack st') = Toploc (Stack st)" using 8(4) unfolding updateStore_def by simp
    then have a20:"\<exists>val. accessStore l (Stack st) = Some val" using t'InDen typeSafeLocExists 2(1) TypeSafe_def by blast
    then have a30:"(\<forall>tloc loc. Toploc (Stack st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Stack st) = None)
                   \<and>(\<forall>loc y. accessStore loc (Stack st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Stack st). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))"
      using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by simp
    then have a40:"(\<forall>tloc loc. Toploc (Stack st') \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Stack st) = None)
                    \<and>(\<forall>loc y. accessStore loc (Stack st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Stack st'). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))"
      using a10 by simp
    show "lessThanTopLocs (Stack st')" unfolding lessThanTopLocs_def
    proof intros
      fix tloc loc
      assume *:"Toploc (Stack st') \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
      then show "accessStore loc (Stack st') = None"
      proof(cases "loc = l")
        case True
        then show ?thesis using * a10
          by (metis a20 a30 option.distinct(1))
      next
        case False
        then have a50:"accessStore loc (Stack st) = accessStore loc (Stack st')" using 8(4) unfolding updateStore_def accessStore_def by simp
        then show ?thesis using 2(1) a40 * a10 False a30 by simp
      qed
    next
      fix loc y
      assume *:" accessStore loc (Stack st') = Some y "
      show "\<exists>tloc<Toploc (Stack st'). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
      proof(cases "loc = l")
        case True
        then show ?thesis using *a10 a20 a30 by simp
      next
        case False
        then have a50:"accessStore loc (Stack st) = accessStore loc (Stack st')" using 8(4) unfolding updateStore_def accessStore_def by simp
        then show ?thesis using * 2(1) a40 by simp
      qed
    qed
  next
    show "lessThanTopLocs cd" using 2(1) unfolding TypeSafe_def using 8 by auto
  next
    show "lessThanTopLocs (Memory st')" using 2(1) unfolding TypeSafe_def using 8 by auto
  next
    have "envAddressesWellFormed env" using 2(1) unfolding TypeSafe_def by auto
    then show "addressFormat (Address env)" and "addressFormat (Sender env)" by simp+
  next
    show "AddressTypes (Accounts st')" using 2(1) unfolding TypeSafe_def using 8 by simp
  next
    have "Accounts st'= Accounts st" using 8 by auto
    then show "fullyInitialised env (Accounts st') (Stack st')" using 2(3) 8 unfolding fullyInitialised_def accessStore_def updateStore_def by auto
  next
    show "denvalueTypeCorrectness env (Stack st') (Memory st')" unfolding denvalueTypeCorrectness_def
    proof intros
      fix tt ll ptr_loc sub_loc
      assume *:"(type.Memory tt, Stackloc ll) |\<in>| fmran (Denvalue env) \<and> accessStore ll (Stack st') = Some (KMemptr ptr_loc)"
      have SameMemory:"(Memory st) = (Memory st')" using 8 by simp
      have old: "denvalueTypeCorrectness env (Stack st) (Memory st)"
        using 2(1) unfolding TypeSafe_def by blast

      show "case tt of MTArray len arr \<Rightarrow> (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr)

     | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st') = Some (MTValue val) "
      proof(cases "ll = l")
        case True
        then have isMTAr:"tt = (MTArray x t)" using lDen * by auto
        then have isP:"ptr_loc = p" using 8 * True by simp

        then have old2:"\<forall>sub_loc. (case pParentT of
                        MTArray len arr \<Rightarrow>
                          (\<forall>i<len. accessTypeStore (hash pParentPtr (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr)

                        | MTValue val \<Rightarrow> accessTypeStore pParentPtr (Memory st) = Some (MTValue val))"
          using pOrigin old unfolding denvalueTypeCorrectness_def by auto
        have "(\<forall>i<x. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some t)"
        proof(cases "KMemptr p = KMemptr pParentPtr")
          case True
          then have "pParentT = MTArray x t" using pOrigin by auto
          then have "(\<forall>i<x. accessTypeStore (hash pParentPtr (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some t)"
            using old2 by simp
          then have "(\<forall>i<x. accessTypeStore (hash pParentPtr (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some t)"
            using SameMemory by (auto split:option.splits mtypes.splits)
          then show ?thesis using True isP SameMemory by blast
        next
          case False
          then obtain len arr where pt:"(extractValueType (KMemptr p) \<noteq> pParentPtr \<and> pParentT = MTArray len arr \<and>
       CompMemType (Memory (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)) len arr (MTArray x t) pParentPtr
        (extractValueType (KMemptr p)))" using pOrigin by blast
          then have cmpt:" CompMemType (Memory st) len arr (MTArray x t) pParentPtr p" by simp

          have "((case pParentT of MTArray len arr \<Rightarrow>
(\<forall>i<len. accessTypeStore (hash pParentPtr (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr)
       | MTValue val \<Rightarrow> accessTypeStore pParentPtr (Memory st) = Some (MTValue val)))"
            using 2(1) pOrigin unfolding TypeSafe_def denvalueTypeCorrectness_def by auto
          then have pPrntAccT:"\<forall>i<len. accessTypeStore (hash pParentPtr (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr"
            using pt by simp

          then have o2:"(\<forall>locs tp.
      accessTypeStore locs (Memory st) = Some tp \<longrightarrow>
      (case accessStore locs (Memory st) of None \<Rightarrow> False
       | Some (MValue v) \<Rightarrow> \<exists>val. MCon tp (Memory st) locs \<and> tp = MTValue val \<and> accessTypeStore locs (Memory st) = Some tp
       | Some (MPointer p) \<Rightarrow> \<exists>len arr. MCon tp (Memory st) p \<and> tp = MTArray len arr
                              \<and> (\<forall>i<len. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr)
                              ))"
            using 2(1) unfolding TypeSafe_def subPrefixStructuralConsistency_def using pt by blast
          have mcPrnt:"MCon (MTArray len arr) (Memory st) pParentPtr"
            using pt pOrigin 2(1) sameMemTSafe[OF 2(1), of pParentPtr] by auto

          have conc1:" \<forall>i<x. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some t"
            using CompMemTypeSubIndexes[OF cmpt _ mcPrnt pPrntAccT] 2(1) unfolding TypeSafe_def by simp
          then show ?thesis
            by (simp add: isP memorySame)
        qed

        then show ?thesis using isMTAr
          using mtypes.simps(5) \<open>\<forall>i<x. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some t\<close> by blast
      next
        case False
        then have "accessStore ll (Stack st) = accessStore ll (Stack st')" using stackChanged by blast
        then have "(case tt of
                    MTArray len arr \<Rightarrow> (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr)

                    | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st) = Some (MTValue val))"
          using old unfolding denvalueTypeCorrectness_def using * by auto
        then show ?thesis using SameMemory by metis
      qed
    qed
  next
    show "subPrefixStructuralConsistency (Memory st')" using 8 2(1) unfolding TypeSafe_def by simp
  next
    show "SomeValSomeTyp (Memory st')" using 2(1) unfolding TypeSafe_def using 8 by simp
  next
    show "\<And>locs t. accessTypeStore locs (Memory st) = Some t \<Longrightarrow> accessTypeStore locs (Memory st') = Some t"
      using 2(1) unfolding TypeSafe_def using 8 by simp
  next
    show "\<And>locs v. accessStore locs (Memory st) = Some (MPointer v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MPointer v')"
      using memorySame by fastforce
  next
    show "\<And>locs v. accessStore locs (Memory st) = Some (MValue v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MValue v')"
      using memorySame by fastforce
  next
    show " \<And>i loc. i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<Longrightarrow> accessStore loc
        (Memory st) = None \<Longrightarrow> accessStore loc (Memory st') = None"
      using memorySame by simp
  next
    show "Toploc (Memory st) \<le> Toploc (Memory st')" using memorySame by auto
  qed
qed

text \<open>Assignment case 9: a memory array assigned to a storage variable reached through a stack pointer: the array is copied into storage.\<close>

lemma TypeSafe_Assign_9:
  assumes "TypeSafe env (Accounts st) (Stack st) (Memory st) (Storage st) cd"
    and "stmt (ASSIGN lv ex) env cd st = Normal ((), st')"
    and "fullyInitialised env (Accounts st) (Stack st)"
    and "expr ex env cd (st\<lparr>state.Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>) (state.Gas st - costs (ASSIGN lv
        ex) env cd st) = Normal ((KMemptr p, type.Memory (MTArray x t)), g)"
    and "lexp lv env cd (st\<lparr>state.Gas := g\<rparr>) g = Normal((LStackloc l, type.Storage t'),g')"
    and "cps2mTypeCompatible t' (MTArray x t)"
    and "accessStore l (Stack st) = Some (KStoptr p')"
    and "cpm2s p p' x t (Memory st) (Storage st (Address env)) = Some s"
    and "st' = st\<lparr>state.Gas := g', Storage := (Storage st) (Address env := s)\<rparr>"
  shows "StateInvariant env st st' cd"
proof -
  let ?case = "StateInvariant env st st' cd"
  note 2 = assms(1-3)
  note 9 = assms(4-9)

  obtain t''' where t''Def:"t' = STArray x t''' " using 9(3)
    by (metis stypes.exhaust cps2mTypeCompatible.simps(2,4,6))
  have sameStack:"(Stack st) = (Stack st')" using 9 unfolding accessStore_def updateStore_def by auto
  have sameMemory:"Memory st' = Memory st " using 9 by auto
  have lInDen:"(type.Storage t', Stackloc l) |\<in>| fmran (Denvalue env)" using lexpStackloc_imps_inDen[of lv env cd ] 9(2) by simp
  have nonLocChanged:"\<forall>t' locs. \<not> LSubPrefL2 locs p' \<or> locs = p' \<longrightarrow> accessStorage t' locs (Storage st (Address env)) = accessStorage t' locs s"
    using 9 unfolding cpm2s_def using cpm2sSingleChange[of p p' t "Memory st" "(Storage st (Address env))" x s]
    by fastforce
  have a30:" \<forall>locs t' t''.
     cps2mTypeCompatible (STArray x t') (MTArray x t) \<and> locs \<noteq> p' \<and> \<not> TypedStoSubpref locs p' (STArray x t') \<longrightarrow>
     accessStorage t'' locs (Storage st (Address env)) = accessStorage t'' locs s"
    using 9(5) unfolding cpm2s_def using cpm2sSingleChange_typedPref[of p "p'" t "Memory st" "(Storage st (Address env))" x s ] by simp
  then have a35:"\<forall>locs t''. locs \<noteq> p' \<and> \<not> TypedStoSubpref locs p' (STArray x t''') \<longrightarrow>
     accessStorage t'' locs (Storage st (Address env)) = accessStorage t'' locs (Storage st' (Address env))"
    using 9 t''Def by auto
  have mInStd:"s = Storage st' (Address env)" using 9 by simp

  have p'MCon:"SCon t' p' (Storage st (Address env))" using 2 9 unfolding TypeSafe_def typeCompat_def using lInDen
    by (auto split:denvalue.splits option.splits stackvalue.splits type.splits)

  have MConsrc:"MCon (MTArray x t) (Memory (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)) (extractValueType (KMemptr p)) \<and>
      (\<exists>xx. KMemptr p = KMemptr xx) \<and>
      (\<exists>stloc tp'' pa.
          (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue env) \<and>
          accessStore stloc (Stack (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)) = Some (KMemptr pa) \<and>
          (tp'' = (MTArray x t) \<and> KMemptr p = KMemptr pa \<or>
           (\<exists>len arr.
               extractValueType (KMemptr p) \<noteq> pa \<and>
               tp'' = MTArray len arr \<and> CompMemType (Memory (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)) len arr (MTArray x t) pa (extractValueType (KMemptr p)))))"
    using 2(1) 9(1) exprTypeconInduct(3)[of ex env cd "(st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)"
        "(state.Gas st - costs (ASSIGN lv ex) env cd st)" "KMemptr p" "type.Memory (MTArray x t)" g]
      2(3) unfolding fullyInitialised_def
    by (auto split:type.splits if_splits )

  note limitSt1 = TypeSafe_memory_bounds(1)[OF 2(1)]
  note limitSt = TypeSafe_memory_bounds(2)[OF 2(1)]
  moreover have allocateSame:"\<forall>loc. accessStore loc (Memory st) = accessStore loc (snd (allocate (Memory st)))" using allocateSameAccess by blast
  ultimately have "accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (snd (allocate (Memory st))) = None" using LSubPrefL2_def by auto
  then have SCondest:"SCon (STArray x t''') p' s" using 9 unfolding cpm2s_def
    using MCon_cpm2s[of p p' t "Memory st" "(Storage st (Address env))" x s t'''] t''Def MConsrc extractValueType.simps(2) by simp
  then have SCondest2:"SCon (STArray x t''') p' (Storage st' (Address env))"
    by (simp add: mInStd)
  then have SCondest3:"SCon t' p' (Storage st' (Address env))"
    by (simp add: mInStd t''Def)

  have stackDenvalLimits:"\<forall>struct loc stloc. (type.Memory struct, Stackloc loc) |\<in>| fmran (Denvalue env)
                          \<and> accessStore loc (Stack st) = Some (KMemptr stloc) \<longrightarrow> \<not> LSubPrefL2 stloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))"
    using typeSafe_noDenElementOverToploc_mem[OF 2(1)] by auto

  show ?thesis unfolding TypeSafe_def StateInvariant_def
  proof intros
    show "AddressTypes (Accounts st')" using 2(1) 9 unfolding TypeSafe_def by simp
  next
    show "unique_locations (Denvalue env)" using 2(1) unfolding TypeSafe_def by simp
  next
    have a0:" compPointers (Stack st) (Denvalue env)" using 2(1) unfolding TypeSafe_def by blast
    show "compPointers (Stack st') (Denvalue env)" unfolding compPointers_def
    proof(intros)
      fix tp1 tp2 l1 l2 l1' l2' stl1 stl2
      assume a1:"(type.Storage tp1, l1) |\<in>| fmran (Denvalue env) \<and>
     (type.Storage tp2, l2) |\<in>| fmran (Denvalue env) \<and>
     (l1 = Stackloc l1' \<and> accessStore l1' (Stack st') = Some (KStoptr stl1) \<or> l1 = Storeloc stl1) \<and> (l2 = Stackloc l2'
         \<and> accessStore l2' (Stack st') = Some (KStoptr stl2) \<or> l2 = Storeloc stl2)"
      then show " if TypedStoSubpref stl2 stl1 tp1 then CompStoType tp1 tp2 stl1 stl2 else if TypedStoSubpref stl1 stl2 tp2 then CompStoType tp2 tp1 stl2 stl1 else True"
      proof(cases "TypedStoSubpref stl2 stl1 tp1")
        case True
        then show ?thesis using a1 sameStack a0 unfolding compPointers_def by simp
      next
        case f1:False
        then show ?thesis
        proof(cases "TypedStoSubpref stl1 stl2 tp2")
          case True
          then show ?thesis using a1 sameStack a0 unfolding compPointers_def by simp
        next
          case False
          then show ?thesis using f1 by simp
        qed
      qed
    qed
  next
    have scOld:"safeContract (Accounts st) (Storage st)" using 2(1) unfolding TypeSafe_def by simp

    show "safeContract (Accounts st') (Storage st')" unfolding safeContract_def
    proof intros
      fix e ct dud i tp
      assume *:"Type (Accounts st' (Address (e::environment))) = Some (atype.Contract (Contract e)) \<and>
               ep $$ Contract (e::environment) = Some (ct, dud) \<and>
               ct $$ i = Some (Var tp)"
      show "SCon tp i (Storage st' (Address e))"
      proof (cases "Address e = Address env")
        case False
        then have sameAddr:"Storage st' (Address e) = Storage st (Address e)" using 9 by simp
        moreover have "SCon tp i (Storage st (Address e))"
          using * scOld 9 unfolding safeContract_def by fastforce
        ultimately show ?thesis by simp
      next
        case addrEq:True
        have typedOld:"Type (Accounts st (Address e)) = Some (atype.Contract (Contract e))"
          using * 9 by simp
        have epOld:"ep $$ Contract e = Some (ct, dud)"
          using * by simp
        have ctOld:"ct $$ i = Some (Var tp)"
          using * by simp
        have denI:"Denvalue env $$ i = Some (type.Storage tp, Storeloc i)"
          using fi_contract_var_to_denvalue_storeloc[OF 2(3) addrEq typedOld epOld ctOld] .
        have inDenI:"(type.Storage tp, Storeloc i) |\<in>| fmran (Denvalue env)"
          using denI by (simp add: fmranI)
        have oldSConE:"SCon tp i (Storage st (Address e))"
          using scOld typedOld epOld ctOld unfolding safeContract_def by blast
        have oldSCon:"SCon tp i (Storage st (Address env))"
          using oldSConE addrEq by simp
        have cmpPtr:"(if TypedStoSubpref p' i tp then CompStoType tp t' i p'
                       else if TypedStoSubpref i p' t' then CompStoType t' tp p' i else True)"
          using 2(1) 9(3) inDenI lInDen t''Def unfolding TypeSafe_def compPointers_def
          using "9"(4) by blast
        have newSCon:"SCon tp i (Storage st' (Address env))"
          using SCon_update_array_subloc_cases[OF cmpPtr SCondest2 SCondest3 oldSCon t''Def a35] .
        show ?thesis using newSCon addrEq by simp
      qed
    qed
  next
    show "balanceTypes (Accounts st')" using 9 using 2(1) unfolding TypeSafe_def by simp
  next
    have "envAddressesWellFormed env" using 2(1) unfolding TypeSafe_def by simp
    then show "addressFormat (Address env)" and "addressFormat (Sender env)" by simp+
  next
    show "svalueTypes (Svalue env)" using 2(1) unfolding TypeSafe_def by simp
  next
    have *:"((\<forall>tloc loc. Toploc (Stack st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Stack st) = None) \<and>
            (\<forall>loc y. accessStore loc (Stack st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Stack st). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))) "
      using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by simp
    have **:"Toploc (Stack st) = Toploc (Stack st')" using 9 unfolding updateStore_def by auto
    show "lessThanTopLocs (Stack st')" using sameStack * ** unfolding lessThanTopLocs_def by auto
  next
    show "lessThanTopLocs cd" using 2(1) unfolding TypeSafe_def by simp
  next
    show "lessThanTopLocs (Memory st')" using sameMemory unfolding lessThanTopLocs_def
      by (simp add: limitSt limitSt1)
  next
    show "typeCompat (Denvalue env) (Stack st') (Memory st') (Storage st' (Address env)) cd"
      unfolding typeCompat_def
    proof intros
      fix t'' l'
      assume inDen:" (t'', l') |\<in>| fmran (Denvalue env)"

      show " denvalueCon (Stack st') (Memory st') (Storage st' (Address env)) cd t'' l'"
      proof(cases l')
        case (Stackloc x1)
        then obtain a where adef:"accessStore x1 (Stack st') = Some a" using inDen Stackloc 2(1) unfolding TypeSafe_def typeCompat_def using sameStack by fastforce
        then show ?thesis
        proof(cases "a")
          case (KValue x1)
          then show ?thesis using Stackloc adef inDen Stackloc 2(1) sameStack unfolding TypeSafe_def typeCompat_def
            by (metis (no_types, lifting) denvalue.simps(5) Option.option.simps(5) stackvalue.simps(17) )
        next
          case (KCDptr x2)
          then show ?thesis using Stackloc adef inDen Stackloc 2(1) sameStack unfolding TypeSafe_def typeCompat_def
            by (metis (no_types, lifting) denvalue.simps(5) Option.option.simps(5) stackvalue.simps(18))
        next
          case (KMemptr x3)
          then show ?thesis using Stackloc adef inDen Stackloc 2(1) sameStack sameMemory unfolding TypeSafe_def typeCompat_def by (cases t''; fastforce)
        next
          case (KStoptr x4)
          then obtain struct where structDef: "t'' = type.Storage struct"
            using Stackloc adef inDen Stackloc 2(1) sameStack
            unfolding TypeSafe_def typeCompat_def
            by (cases t''; fastforce)

          have cmpStoPtr:"(
            (type.Storage struct, l') |\<in>| fmran (Denvalue env) \<and>
            (type.Storage (STArray x t'''), Stackloc l) |\<in>| fmran (Denvalue env) \<and>
            (l' = Stackloc x1 \<and> accessStore x1 (Stack st) = Some (KStoptr x4) \<or> l' = Storeloc x4) \<and>
            (accessStore l (Stack st) = Some (KStoptr p')) \<longrightarrow>
            (if TypedStoSubpref p' x4 struct then CompStoType struct (STArray x t''') x4 p'
             else if TypedStoSubpref x4 p' (STArray x t''') then CompStoType (STArray x t''') struct p' x4 else True))"
            using 2(1) 9(3) lInDen inDen Stackloc structDef KStoptr unfolding TypeSafe_def compPointers_def by blast

          then have cmpStoPtr2:"(if TypedStoSubpref p' x4 struct then CompStoType struct (STArray x t''') x4 p'
           else if TypedStoSubpref x4 p' (STArray x t''') then CompStoType (STArray x t''') struct p' x4 else True)"
            using 9(4) lInDen inDen Stackloc structDef KStoptr t''Def
            by (simp add: adef sameStack)

          have SConx4Old:"SCon struct x4 (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using Stackloc adef inDen Stackloc 2(1) sameStack structDef KStoptr
            by fastforce

          have "SCon struct x4 (Storage st' (Address env))"
          proof(cases "TypedStoSubpref p' x4 struct")
            case True
            then have "CompStoType struct (STArray x t''') x4 p'" using cmpStoPtr2 by simp
            then show ?thesis using SCondest2 SConx4Old a35 t''Def TypedStoSubpref_shared_parent_related SCon_sub_imps_Parent
              by blast

          next
            case f1:False
            then show ?thesis
            proof(cases "TypedStoSubpref x4 p' (STArray x t''')")
              case True
              then have "CompStoType t' struct p' x4 " using cmpStoPtr2 f1 t''Def by simp
              then show ?thesis using SCondest3 SCon_imps_sublocs by blast

            next
              case False
              have notSame:"x4 \<noteq> p'" using False by auto
              have k7:"\<forall>locs. TypedStoSubpref locs x4 struct \<longrightarrow> locs \<noteq> p' " using f1 by blast
              have k8:"\<forall>locs. TypedStoSubpref locs p' (STArray x t''') \<longrightarrow> locs \<noteq> x4" using False by auto
              show ?thesis using sublocs_nonchanged_SCon[OF f1 a35 SConx4Old False] by blast
            qed
          qed
          then show ?thesis using Stackloc adef inDen Stackloc 2(1) sameStack KStoptr structDef by simp
        qed

      next
        case (Storeloc x2)
        then obtain struct where structDef: "t'' = type.Storage struct" using Storeloc inDen 2(1) sameStack unfolding TypeSafe_def typeCompat_def
          by (cases t''; fastforce)

        have cmpStoPtr:"(
            (type.Storage struct, l') |\<in>| fmran (Denvalue env) \<and>
            (type.Storage (STArray x t'''), Stackloc l) |\<in>| fmran (Denvalue env) \<and>
             l' = Storeloc x2) \<and>
            (accessStore l (Stack st) = Some (KStoptr p')) \<longrightarrow>
            (if TypedStoSubpref p' x2 struct then CompStoType struct (STArray x t''') x2 p'
             else if TypedStoSubpref x2 p' (STArray x t''') then CompStoType (STArray x t''') struct p' x2 else True)"
          using 2(1) 9(3) lInDen inDen Storeloc structDef unfolding TypeSafe_def compPointers_def by blast

        then have cmpStoPtr2:"(if TypedStoSubpref p' x2 struct then CompStoType struct (STArray x t''') x2 p'
             else if TypedStoSubpref x2 p' (STArray x t''') then CompStoType (STArray x t''') struct p' x2 else True)"
          using 9(4) lInDen inDen Storeloc structDef t''Def by (simp add: sameStack)

        have SConx4Old:"SCon struct x2 (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using Storeloc inDen 2(1) sameStack structDef
          by fastforce

        have "SCon struct x2 (Storage st' (Address env))"
        proof(cases "TypedStoSubpref p' x2 struct")
          case True
          then have "CompStoType struct (STArray x t''') x2 p'" using cmpStoPtr2 by simp
          then show ?thesis using SCondest2 SConx4Old a35 t''Def TypedStoSubpref_shared_parent_related SCon_sub_imps_Parent
            by blast
        next
          case f1:False
          then show ?thesis
          proof(cases "TypedStoSubpref x2 p' (STArray x t''')")
            case True
            then have "CompStoType t' struct p' x2 " using cmpStoPtr2 f1 t''Def by simp
            then show ?thesis using SCondest3 SCon_imps_sublocs by blast
          next
            case False
            have notSame:"x2 \<noteq> p'" using False by auto
            have k7:"\<forall>locs. TypedStoSubpref locs x2 struct \<longrightarrow> locs \<noteq> p' " using f1 by blast
            have k8:"\<forall>locs. TypedStoSubpref locs p' (STArray x t''') \<longrightarrow> locs \<noteq> x2" using False by auto
            show ?thesis using sublocs_nonchanged_SCon[OF f1 a35 SConx4Old False] by blast
          qed
        qed
        then show ?thesis using Storeloc inDen 2(1) sameStack Storeloc structDef by simp
      qed
    qed
    then have "typeCompat (Denvalue env) (Stack st) (Memory st') (Storage st' (Address env)) cd" using sameStack by simp
  next
    have "Accounts st'= Accounts st" using 9 by auto
    then show "fullyInitialised env (Accounts st') (Stack st')" using 2(3) 9 unfolding fullyInitialised_def by auto
  next
    have cc0:"\<forall>l ptr_loc. accessStore l (Stack st') = Some (KMemptr ptr_loc) \<longrightarrow> accessStore l (Stack st) = Some (KMemptr ptr_loc)"
      using 9(6) unfolding updateStore_def accessStore_def by auto
    show "denvalueTypeCorrectness env (Stack st') (Memory st')"

      unfolding denvalueTypeCorrectness_def
    proof intros
      fix t l ptr_loc sub_loc
      assume "(type.Memory t, Stackloc l) |\<in>| fmran (Denvalue env) \<and>
     accessStore l (Stack st') = Some (KMemptr ptr_loc)"
      then have "(case t of
      MTArray len arr \<Rightarrow>
         (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr)
       | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st) = Some (MTValue val))"
        using 2(1) unfolding TypeSafe_def denvalueTypeCorrectness_def using cc0 by blast
      moreover have "Memory st = Memory st'" using 9(6) by simp
      ultimately show "case t of
     MTArray len arr \<Rightarrow>
      (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr)
     | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st') = Some (MTValue val)"
        by metis
    qed
  next
    show "subPrefixStructuralConsistency (Memory st')" using 2(1) unfolding TypeSafe_def using 9(6) by auto
  next
    show "SomeValSomeTyp (Memory st')" using 2(1) unfolding TypeSafe_def using 9(6) by auto
  next
    show "\<And>locs t. accessTypeStore locs (Memory st) = Some t \<Longrightarrow> accessTypeStore locs (Memory st') = Some t "
      using 2(1) unfolding TypeSafe_def using 9(6) by auto
  next
    show "\<And>locs v. accessStore locs (Memory st) = Some (MPointer v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MPointer v')"
      using 9(6) by simp
  next
    show "\<And>locs v. accessStore locs (Memory st) = Some (MValue v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MValue v')"
      using 9(6) by simp
  next
    show " \<And>i loc. i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<Longrightarrow> accessStore loc
        (Memory st) = None \<Longrightarrow> accessStore loc (Memory st') = None"
      using 9(6) by simp
  next
    show "Toploc (Memory st) \<le> Toploc (Memory st')" using 9(6) by simp
  qed
qed

text \<open>Assignment case 10: a memory array assigned to a storage location: the array is copied into storage.\<close>

lemma TypeSafe_Assign_10:
  assumes "TypeSafe env (Accounts st) (Stack st) (Memory st) (Storage st) cd"
    and "stmt (ASSIGN lv ex) env cd st = Normal ((), st')"
    and "fullyInitialised env (Accounts st) (Stack st)"
    and "expr ex env cd (st\<lparr>state.Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>) (state.Gas st - costs (ASSIGN lv
        ex) env cd st) = Normal ((KMemptr p, type.Memory (MTArray x t)), g)"
    and "lexp lv env cd (st\<lparr>state.Gas := g\<rparr>) g = Normal((LStoreloc l, type.Storage t'),g')"
    and "cps2mTypeCompatible t' (MTArray x t)"
    and "cpm2s p l x t (Memory st) (Storage st (Address env)) = Some s"
    and "st' = st\<lparr>state.Gas := g', Storage := (Storage st) (Address env := s)\<rparr>"
  shows "StateInvariant env st st' cd"
proof -
  let ?case = "StateInvariant env st st' cd"
  note 2 = assms(1-3)
  note 10 = assms(4-8)

  obtain t''' where t''Def:"t' = STArray x t''' " using 10(3)
    by (metis stypes.exhaust cps2mTypeCompatible.simps(2,4,6))
  have sameStack:"(Stack st) = (Stack st')" using 10 unfolding accessStore_def updateStore_def by auto
  have sameMemory:"Memory st' = Memory st " using 10 by auto
  have nonLocChanged:"\<forall>t' locs. \<not> LSubPrefL2 locs l \<or> locs = l \<longrightarrow> accessStorage t' locs (Storage st (Address env)) = accessStorage t' locs s"
    using 10(4) unfolding cpm2s_def using cpm2sSingleChange[of p l t "Memory st" "(Storage st (Address env))" x s]
    by fastforce
  have a30:" \<forall>locs t' t''.
     cps2mTypeCompatible (STArray x t') (MTArray x t) \<and> locs \<noteq> l \<and> \<not> TypedStoSubpref locs l (STArray x t') \<longrightarrow>
     accessStorage t'' locs (Storage st (Address env)) = accessStorage t'' locs s"
    using 10(4) unfolding cpm2s_def using cpm2sSingleChange_typedPref[of p "l" t "Memory st" "(Storage st (Address env))" x s ]
    by simp
  then have a35:"\<forall>locs t''. locs \<noteq> l \<and> \<not> TypedStoSubpref locs l (STArray x t''') \<longrightarrow>
     accessStorage t'' locs (Storage st (Address env)) = accessStorage t'' locs (Storage st' (Address env))"
    using 10 t''Def by auto
  have mInStd:"s = Storage st' (Address env)" using 10 by simp

  have MConsrc:"MCon (MTArray x t) (Memory (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)) (extractValueType (KMemptr p)) \<and>
      (\<exists>xx. KMemptr p = KMemptr xx) \<and>
      (\<exists>stloc tp'' pa.
          (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue env) \<and>
          accessStore stloc (Stack (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)) = Some (KMemptr pa) \<and>
          (tp'' = (MTArray x t) \<and> KMemptr p = KMemptr pa \<or>
           (\<exists>len arr.
               extractValueType (KMemptr p) \<noteq> pa \<and>
               tp'' = MTArray len arr \<and> CompMemType (Memory (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)) len arr (MTArray x t) pa (extractValueType (KMemptr p)))))"
    using 2(1) 10(1) exprTypeconInduct(3)[of ex env cd "(st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)"
        "(state.Gas st - costs (ASSIGN lv ex) env cd st)" "KMemptr p" "type.Memory (MTArray x t)" g]
    using 2(3) unfolding fullyInitialised_def
    by (auto split:type.splits if_splits )

  note limitSt1 = TypeSafe_memory_bounds(1)[OF 2(1)]
  note limitSt = TypeSafe_memory_bounds(2)[OF 2(1)]
  moreover have allocateSame:"\<forall>loc. accessStore loc (Memory st) = accessStore loc (snd (allocate (Memory st)))" using allocateSameAccess by blast
  ultimately have "accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (snd (allocate (Memory st))) = None" using LSubPrefL2_def by auto
  then have SCondest:"SCon (STArray x t''') l s" using 10 unfolding cpm2s_def
    using MCon_cpm2s[of p l t "Memory st" "(Storage st (Address env))" x s t'''] t''Def MConsrc extractValueType.simps(2) by auto
  then have SCondest2:"SCon (STArray x t''') l (Storage st' (Address env))"
    by (simp add: mInStd)
  then have SCondest3:"SCon t' l (Storage st' (Address env))"
    by (simp add: mInStd t''Def)

  have stackDenvalLimits:"\<forall>struct loc stloc. (type.Memory struct, Stackloc loc) |\<in>| fmran (Denvalue env)
                          \<and> accessStore loc (Stack st) = Some (KMemptr stloc) \<longrightarrow> \<not> LSubPrefL2 stloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))"
    using typeSafe_noDenElementOverToploc_mem[OF 2(1)] by auto

  show ?thesis unfolding TypeSafe_def StateInvariant_def
  proof intros
    show "AddressTypes (Accounts st')" using 2(1) 10 unfolding TypeSafe_def by simp
  next
    show "unique_locations (Denvalue env)" using 2(1) unfolding TypeSafe_def by simp
  next
    have a0:" compPointers (Stack st) (Denvalue env)" using 2(1) unfolding TypeSafe_def by blast
    show "compPointers (Stack st') (Denvalue env)" unfolding compPointers_def
    proof(intros)
      fix tp1 tp2 l1 l2 l1' l2' stl1 stl2
      assume a1:"(type.Storage tp1, l1) |\<in>| fmran (Denvalue env) \<and>
     (type.Storage tp2, l2) |\<in>| fmran (Denvalue env) \<and>
     (l1 = Stackloc l1' \<and> accessStore l1' (Stack st') = Some (KStoptr stl1) \<or> l1 = Storeloc stl1) \<and> (l2 = Stackloc l2'
         \<and> accessStore l2' (Stack st') = Some (KStoptr stl2) \<or> l2 = Storeloc stl2)"
      then show " if TypedStoSubpref stl2 stl1 tp1 then CompStoType tp1 tp2 stl1 stl2 else if TypedStoSubpref stl1 stl2 tp2 then CompStoType tp2 tp1 stl2 stl1 else True"
      proof(cases "TypedStoSubpref stl2 stl1 tp1")
        case True
        then show ?thesis using a1 sameStack a0 unfolding compPointers_def by simp
      next
        case f1:False
        then show ?thesis
        proof(cases "TypedStoSubpref stl1 stl2 tp2")
          case True
          then show ?thesis using a1 sameStack a0 unfolding compPointers_def by simp
        next
          case False
          then show ?thesis using f1 by simp
        qed
      qed
    qed
  next
    have scOld:"safeContract (Accounts st) (Storage st)" using 2(1) unfolding TypeSafe_def by simp

    show "safeContract (Accounts st') (Storage st')" unfolding safeContract_def
    proof intros
      fix e ct dud i tp
      assume *:"Type (Accounts st' (Address (e::environment))) = Some (atype.Contract (Contract e)) \<and>
               ep $$ Contract (e::environment) = Some (ct, dud) \<and>
               ct $$ i = Some (Var tp)"
      show "SCon tp i (Storage st' (Address e))"
      proof (cases "Address e = Address env")
        case False
        then have sameAddr:"Storage st' (Address e) = Storage st (Address e)" using 10 by simp
        moreover have "SCon tp i (Storage st (Address e))"
          using * scOld 10 unfolding safeContract_def by fastforce
        ultimately show ?thesis by simp
      next
        case addrEq:True
        have typedOld:"Type (Accounts st (Address e)) = Some (atype.Contract (Contract e))"
          using * 10 by simp
        have epOld:"ep $$ Contract e = Some (ct, dud)"
          using * by simp
        have ctOld:"ct $$ i = Some (Var tp)"
          using * by simp
        have denI:"Denvalue env $$ i = Some (type.Storage tp, Storeloc i)"
          using fi_contract_var_to_denvalue_storeloc[OF 2(3) addrEq typedOld epOld ctOld] .
        have inDenI:"(type.Storage tp, Storeloc i) |\<in>| fmran (Denvalue env)"
          using denI by (simp add: fmranI)
        have oldSConE:"SCon tp i (Storage st (Address e))"
          using scOld typedOld epOld ctOld unfolding safeContract_def by blast
        have oldSCon:"SCon tp i (Storage st (Address env))"
          using oldSConE addrEq by simp
        have uniq:"unique_locations (Denvalue env)"
          using 2(1) typeSafeUnique by simp
        have epEnv:"ep $$ Contract env = Some (ct, dud)"
          using epOld addrEq
          using 2(3) fullyInitialised_def typedOld by auto
        show ?thesis
        proof(cases rule:lexpStorageG[OF 2(1) 10(2) 2(3)])
          case lInDen:1
          have inDenL:"(type.Storage t', Storeloc l) |\<in>| fmran (Denvalue env)"
            using lInDen by simp
          have cmpPtr:"(if TypedStoSubpref l i tp then CompStoType tp t' i l
                        else if TypedStoSubpref i l t' then CompStoType t' tp l i else True)"
            using 2(1) 10(3) inDenI inDenL unfolding TypeSafe_def compPointers_def by blast
          have newSCon:"SCon tp i (Storage st' (Address env))"
            using SCon_update_array_subloc_cases[OF cmpPtr SCondest2 SCondest3 oldSCon t''Def a35] .
          show ?thesis using newSCon addrEq by simp
        next
          case sub2:(2 l''' t)
          have inDenL:"(type.Storage t, Storeloc l''') |\<in>| fmran (Denvalue env)" using sub2 by simp
          have relL:"TypedStoSubpref l l''' t \<and> CompStoType t t' l''' l" using sub2 by simp
          show ?thesis
          proof(cases "i = l'''")
            case True
            have pairEq:"(type.Storage tp, Storeloc i) = (type.Storage t, Storeloc l''')"
              using uniqueLocs[OF uniq inDenI inDenL] True by simp
            then have tpEq:"tp = t" by simp
            have cmpPtr:"(if TypedStoSubpref l i tp then CompStoType tp t' i l
                          else if TypedStoSubpref i l t' then CompStoType t' tp l i else True)"
              using relL tpEq True by simp
            have newSCon:"SCon tp i (Storage st' (Address env))"
              using SCon_update_array_subloc_cases[OF cmpPtr SCondest2 SCondest3 oldSCon t''Def a35] .
            show ?thesis using newSCon addrEq by simp
          next
            case False
            have ctL:"ct $$ l''' = Some (Var t)"
              using fi_denvalue_storeloc_to_contract_var[OF 2(3) epEnv inDenL] .
            have nPrnt1:"\<not>TypedStoSubpref i l''' t"
                and nPrnt2:"\<not>TypedStoSubpref l''' i tp"
              using methodVarsNoPref False epOld ctOld ctL by blast+
            have n1:"\<not>TypedStoSubpref l i tp"
              using NotRelatedPrnt_imps_notRelatedChild[OF nPrnt1 nPrnt2] relL by blast
            have n2:"\<not>TypedStoSubpref i l t'"
              using NotReachablePrnt_imps_notReachableChild nPrnt1 nPrnt2 relL by blast
            have cmpPtr:"(if TypedStoSubpref l i tp then CompStoType tp t' i l
                          else if TypedStoSubpref i l t' then CompStoType t' tp l i else True)"
              using n1 n2 by simp
            have newSCon:"SCon tp i (Storage st' (Address env))"
              using SCon_update_array_subloc_cases[OF cmpPtr SCondest2 SCondest3 oldSCon t''Def a35] .
            show ?thesis using newSCon addrEq by simp
          qed
        next
          case sub3:(3 l' t l'')
          have inDenStk:"(type.Storage t, Stackloc l'') |\<in>| fmran (Denvalue env)" using sub3 by simp
          have ptrL:"accessStore l'' (Stack st) = Some (KStoptr l')" using sub3 by simp
          have rel0:"TypedStoSubpref l l' t \<and> CompStoType t t' l' l" using sub3 by simp
          obtain tprnt lprnt where
              inDenPr:"(type.Storage tprnt, Storeloc lprnt) |\<in>| fmran (Denvalue env)"
              and compPr:"CompStoType tprnt t lprnt l'"
            using fiPtr_parent_from_fullyInitialised[OF 2(3) inDenStk ptrL] by blast
          have compPr2:"CompStoType tprnt t' lprnt l"
            using compPr rel0 CompStoType_trns by blast
          have relPr:"TypedStoSubpref l lprnt tprnt \<and> CompStoType tprnt t' lprnt l"
            using compPr2 CompStoType_imps_TypedStoSubpref by blast
          show ?thesis
          proof(cases "i = lprnt")
            case True
            have pairEq:"(type.Storage tp, Storeloc i) = (type.Storage tprnt, Storeloc lprnt)"
              using uniqueLocs[OF uniq inDenI inDenPr] True by simp
            then have tpEq:"tp = tprnt" by simp
            have cmpPtr:"(if TypedStoSubpref l i tp then CompStoType tp t' i l
                          else if TypedStoSubpref i l t' then CompStoType t' tp l i else True)"
              using compPr2 tpEq True
              using relPr by presburger
            have newSCon:"SCon tp i (Storage st' (Address env))"
              using SCon_update_array_subloc_cases[OF cmpPtr SCondest2 SCondest3 oldSCon t''Def a35] .
            show ?thesis using newSCon addrEq by simp
          next
            case False
            have ctPr:"ct $$ lprnt = Some (Var tprnt)"
              using fi_denvalue_storeloc_to_contract_var[OF 2(3) epEnv inDenPr] .
            have nPrnt1:"\<not>TypedStoSubpref i lprnt tprnt"
                and nPrnt2:"\<not>TypedStoSubpref lprnt i tp"
              using methodVarsNoPref False epOld ctOld ctPr by blast+
            have n1:"\<not>TypedStoSubpref l i tp"
              using NotRelatedPrnt_imps_notRelatedChild[OF nPrnt1 nPrnt2] relPr by blast
            have n2:"\<not>TypedStoSubpref i l t'"
              using NotReachablePrnt_imps_notReachableChild nPrnt1 nPrnt2 relPr by blast
            have cmpPtr:"(if TypedStoSubpref l i tp then CompStoType tp t' i l
                          else if TypedStoSubpref i l t' then CompStoType t' tp l i else True)"
              using n1 n2 by simp
            have newSCon:"SCon tp i (Storage st' (Address env))"
              using SCon_update_array_subloc_cases[OF cmpPtr SCondest2 SCondest3 oldSCon t''Def a35] .
            show ?thesis using newSCon addrEq by simp
          qed
        qed
      qed
    qed
  next
    show "balanceTypes (Accounts st')" using 10 using 2(1) unfolding TypeSafe_def by simp
  next
    have "envAddressesWellFormed env" using 2(1) unfolding TypeSafe_def by simp
    then show "addressFormat (Address env)" and "addressFormat (Sender env)" by simp+
  next
    show "svalueTypes (Svalue env)" using 2(1) unfolding TypeSafe_def by simp
  next
    have *:"((\<forall>tloc loc. Toploc (Stack st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Stack st) = None) \<and>
            (\<forall>loc y. accessStore loc (Stack st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Stack st). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))) "
      using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by simp
    have **:"Toploc (Stack st) = Toploc (Stack st')" using 10 unfolding updateStore_def by auto
    show "lessThanTopLocs (Stack st')" using sameStack * ** unfolding lessThanTopLocs_def by auto
  next
    show "lessThanTopLocs cd" using 2(1) unfolding TypeSafe_def by simp
  next
    show "lessThanTopLocs (Memory st')" using sameMemory unfolding lessThanTopLocs_def
      by (simp add: limitSt limitSt1)
  next
    show "typeCompat (Denvalue env) (Stack st') (Memory st') (Storage st' (Address env)) cd"
      unfolding typeCompat_def
    proof intros
      fix t'' l'
      assume inDen:" (t'', l') |\<in>| fmran (Denvalue env)"

      show " denvalueCon (Stack st') (Memory st') (Storage st' (Address env)) cd t'' l'"
      proof(cases l')
        case (Stackloc x1)
        then obtain a where adef:"accessStore x1 (Stack st') = Some a" using inDen Stackloc 2(1) unfolding TypeSafe_def typeCompat_def using sameStack by fastforce
        then show ?thesis
        proof(cases "a")
          case (KValue x1)
          then show ?thesis using Stackloc adef inDen Stackloc 2(1) sameStack unfolding TypeSafe_def typeCompat_def
            by (metis (no_types, lifting) denvalue.simps(5) Option.option.simps(5) stackvalue.simps(17) )
        next
          case (KCDptr x2)
          then show ?thesis using Stackloc adef inDen Stackloc 2(1) sameStack unfolding TypeSafe_def typeCompat_def
            by (metis (no_types, lifting) denvalue.simps(5) Option.option.simps(5) stackvalue.simps(18))
        next
          case (KMemptr x3)
          then show ?thesis using Stackloc adef inDen Stackloc 2(1) sameStack sameMemory unfolding TypeSafe_def typeCompat_def by (cases t''; fastforce)
        next
          case (KStoptr x4)
          then obtain struct where structDef: "t'' = type.Storage struct" using Stackloc adef inDen Stackloc 2(1) sameStack unfolding TypeSafe_def typeCompat_def
            by (cases t''; fastforce)

          have "SCon struct x4 (Storage st' (Address env))"
          proof(cases rule:lexpStorageG[OF 2(1) 10(2) 2(3)])
            case lInDen:1
            have cmpStoPtr:"(
              (type.Storage struct, l') |\<in>| fmran (Denvalue env) \<and>
              (type.Storage (STArray x t'''), Storeloc l) |\<in>| fmran (Denvalue env) \<and>
               l' = Stackloc x1 \<and> accessStore x1 (Stack st) = Some (KStoptr x4))
               \<longrightarrow>
              (if TypedStoSubpref l x4 struct then CompStoType struct (STArray x t''') x4 l
               else if TypedStoSubpref x4 l (STArray x t''') then CompStoType (STArray x t''') struct l x4 else True)"
              using 2(1) 10(3) lInDen inDen adef Stackloc KStoptr structDef unfolding TypeSafe_def compPointers_def by blast

            then have cmpStoPtr2:"(if TypedStoSubpref l x4 struct then CompStoType struct (STArray x t''') x4 l
               else if TypedStoSubpref x4 l (STArray x t''') then CompStoType (STArray x t''') struct l x4 else True)"
              using 10(3) lInDen inDen adef Stackloc KStoptr structDef t''Def sameStack by auto

            have SConx4Old:"SCon struct x4 (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using adef Stackloc KStoptr inDen 2(1) sameStack structDef
              by fastforce

            have "SCon struct x4 (Storage st' (Address env))"
            proof(cases "TypedStoSubpref l x4 struct")
              case True
              then have "CompStoType struct (STArray x t''') x4 l" using cmpStoPtr2 by simp
              then show ?thesis using SCondest2 SConx4Old a35 t''Def TypedStoSubpref_shared_parent_related SCon_sub_imps_Parent
                by blast

            next
              case f1:False
              then show ?thesis
              proof(cases "TypedStoSubpref x4 l (STArray x t''')")
                case True
                then have "CompStoType t' struct l x4 " using cmpStoPtr2 f1 t''Def by simp
                then show ?thesis using SCondest3 SCon_imps_sublocs by blast
              next
                case False
                have notSame:"x4 \<noteq> l" using False by auto
                have k7:"\<forall>locs. TypedStoSubpref locs x4 struct \<longrightarrow> locs \<noteq> l " using f1 by blast
                have k8:"\<forall>locs. TypedStoSubpref locs l (STArray x t''') \<longrightarrow> locs \<noteq> x4" using False by auto
                show ?thesis using sublocs_nonchanged_SCon[OF f1 a35 SConx4Old False] by blast
              qed
            qed
            then show ?thesis by simp
          next
            case sub2:(2 l''' t)
            have cmpStoPtr:"(
              (type.Storage struct, l') |\<in>| fmran (Denvalue env) \<and>
              (type.Storage t, Storeloc l''') |\<in>| fmran (Denvalue env) \<and>
               l' = Stackloc x1 \<and> accessStore x1 (Stack st) = Some (KStoptr x4))
               \<longrightarrow>
              (if TypedStoSubpref l''' x4 struct then CompStoType struct t x4 l'''
               else if TypedStoSubpref x4 l''' t then CompStoType t struct l''' x4 else True)"
              using 2(1) 10(3) inDen adef Stackloc KStoptr structDef unfolding TypeSafe_def compPointers_def by blast

            then have cmpStoPtr2:"(if TypedStoSubpref l''' x4 struct then CompStoType struct t x4 l'''
               else if TypedStoSubpref x4 l''' t then CompStoType t struct l''' x4 else True)"
              using 10(3) sub2 inDen adef Stackloc KStoptr structDef t''Def sameStack by auto

            have SConx4Old:"SCon struct x4 (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using adef Stackloc KStoptr inDen 2(1) sameStack structDef
              by fastforce
            have scl''':"SCon t l''' (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using sub2 by fastforce

            have "SCon struct x4 (Storage st' (Address env))"
            proof(cases "TypedStoSubpref l''' x4 struct")
              case True
              then have "CompStoType struct t x4 l'''" using cmpStoPtr2 by simp
              then have "CompStoType struct (STArray x t''') x4 l" using sub2
                using CompStoType_trns t''Def by blast
              then show ?thesis using SCondest2 SConx4Old a35 t''Def TypedStoSubpref_shared_parent_related SCon_sub_imps_Parent
                by blast
            next
              case f1:False
              then show ?thesis
              proof(cases "TypedStoSubpref x4 l''' t")
                case True
                then have "l''' \<noteq> x4" using f1
                  using TypedStoSubpref_sameLoc by auto
                then show ?thesis
                proof(cases "l = x4")
                  case t5:True
                  then have " CompStoType t struct l''' x4" using cmpStoPtr2 f1 t''Def True by simp
                  moreover have "CompStoType t t' l''' x4" using t5 sub2 by auto
                  ultimately have "t' = struct" using CompStoType_sameLocs_sameType
                    by simp
                  then show ?thesis using SCondest3 SCon_imps_sublocs t5 by simp
                next
                  case False
                  then have " CompStoType t struct l''' x4" using cmpStoPtr2 f1 t''Def True by simp
                  then show ?thesis
                  proof(cases "CompStoType t' struct l x4 ")
                    case True
                    then show ?thesis
                      using SCon_imps_sublocs SCondest3 by blast
                  next
                    case False
                    then show ?thesis
                      using SCon_imps_sublocs SCon_sub_imps_Parent SCondest2 \<open>CompStoType t struct l''' x4\<close> a35 scl''' sub2(2) t''Def by blast
                  qed
                qed
              next
                case False
                then have asm10:"\<not> TypedStoSubpref l x4 struct" using NotRelatedPrnt_imps_notRelatedChild[OF False f1 ] sub2 by blast
                then have asm20:"\<not> TypedStoSubpref x4 l t'" using sub2 NotReachablePrnt_imps_notReachableChild False f1 by blast
                have notSame:"x4 \<noteq> l" using False sub2 by blast
                have k7:"\<forall>locs. TypedStoSubpref locs x4 struct \<longrightarrow> locs \<noteq> l " using f1 sub2 asm10 asm20 by blast
                have k8:"\<forall>locs. TypedStoSubpref locs l (STArray x t''') \<longrightarrow> locs \<noteq> x4" using False sub2 t''Def asm10 asm20 by blast
                show ?thesis using sublocs_nonchanged_SCon[OF _ a35 SConx4Old] asm10 asm20 t''Def by blast
              qed
            qed

            then show ?thesis by simp
          next
            case sub3:(3 l''' t l'''')
            have cmpStoPtr:"(
              (type.Storage struct, l') |\<in>| fmran (Denvalue env) \<and>
              (type.Storage t, Stackloc l'''') |\<in>| fmran (Denvalue env) \<and>
               l' = Stackloc x1 \<and> accessStore x1 (Stack st) = Some (KStoptr x4)) \<and> accessStore l'''' (Stack st) = Some (KStoptr l''')
               \<longrightarrow>
              (if TypedStoSubpref l''' x4 struct then CompStoType struct t x4 l'''
               else if TypedStoSubpref x4 l''' t then CompStoType t struct l''' x4 else True)"
              using 2(1) 10(3) inDen adef Stackloc KStoptr structDef unfolding TypeSafe_def compPointers_def by blast

            then have cmpStoPtr2:"(if TypedStoSubpref l''' x4 struct then CompStoType struct t x4 l'''
               else if TypedStoSubpref x4 l''' t then CompStoType t struct l''' x4 else True)"
              using 10(3) sub3 inDen adef Stackloc KStoptr structDef t''Def sameStack by auto

            have SConx4Old:"SCon struct x4 (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using adef Stackloc KStoptr inDen 2(1) sameStack structDef
              by fastforce
            have scl''':"SCon t l''' (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using sub3 by fastforce

            have "SCon struct x4 (Storage st' (Address env))"
            proof(cases "TypedStoSubpref l''' x4 struct")
              case True
              then have "CompStoType struct t x4 l'''" using cmpStoPtr2 by simp
              then have "CompStoType struct (STArray x t''') x4 l" using sub3
                using CompStoType_trns t''Def by blast
              then show ?thesis using SCondest2 SConx4Old a35 t''Def TypedStoSubpref_shared_parent_related SCon_sub_imps_Parent
                by blast
            next
              case f1:False
              then show ?thesis
              proof(cases "TypedStoSubpref x4 l''' t")
                case True
                then have "l''' \<noteq> x4" using f1
                  using TypedStoSubpref_sameLoc by auto
                then show ?thesis
                proof(cases "l = x4")
                  case t5:True
                  then have " CompStoType t struct l''' x4" using cmpStoPtr2 f1 t''Def True by simp
                  moreover have "CompStoType t t' l''' x4" using t5 sub3 by auto
                  ultimately have "t' = struct" using CompStoType_sameLocs_sameType
                    by simp
                  then show ?thesis using SCondest3 SCon_imps_sublocs t5 by simp
                next
                  case False
                  then have " CompStoType t struct l''' x4" using cmpStoPtr2 f1 t''Def True by simp
                  then show ?thesis
                  proof(cases "CompStoType t' struct l x4 ")
                    case True
                    then show ?thesis
                      using SCon_imps_sublocs SCondest3 by blast
                  next
                    case False
                    then show ?thesis
                      using SCon_imps_sublocs SCon_sub_imps_Parent SCondest2 \<open>CompStoType t struct l''' x4\<close> a35 scl''' sub3(3) t''Def by blast
                  qed
                qed
              next
                case False
                then have asm10:"\<not> TypedStoSubpref l x4 struct" using NotRelatedPrnt_imps_notRelatedChild[OF False f1 ] sub3 by blast
                then have asm20:"\<not> TypedStoSubpref x4 l t'" using sub3 NotReachablePrnt_imps_notReachableChild False f1 by blast
                have notSame:"x4 \<noteq> l" using False sub3 by blast
                have k7:"\<forall>locs. TypedStoSubpref locs x4 struct \<longrightarrow> locs \<noteq> l " using f1 sub3 asm10 asm20 by blast
                have k8:"\<forall>locs. TypedStoSubpref locs l (STArray x t''') \<longrightarrow> locs \<noteq> x4" using False sub3 t''Def asm10 asm20 by blast
                show ?thesis using sublocs_nonchanged_SCon[OF _ a35 SConx4Old] asm10 asm20 t''Def by blast
              qed
            qed
            then show ?thesis by simp
          qed
          then show ?thesis using Stackloc inDen 2(1) sameStack KStoptr adef structDef by simp
        qed
      next
        case (Storeloc x2)
        then obtain struct where structDef: "t'' = type.Storage struct" using Storeloc inDen 2(1) sameStack unfolding TypeSafe_def typeCompat_def
          by (cases t''; fastforce)

        have "SCon struct x2 (Storage st' (Address env))"
        proof(cases rule:lexpStorageG[OF 2(1) 10(2) 2(3)])
          case lInDen:1
          have cmpStoPtr:"(
            (type.Storage struct, l') |\<in>| fmran (Denvalue env) \<and>
            (type.Storage (STArray x t'''), Storeloc l) |\<in>| fmran (Denvalue env) \<and>
             l' = Storeloc x2)
             \<longrightarrow>
            (if TypedStoSubpref l x2 struct then CompStoType struct (STArray x t''') x2 l
             else if TypedStoSubpref x2 l (STArray x t''') then CompStoType (STArray x t''') struct l x2 else True)"
            using 2(1) 10(3) lInDen inDen Storeloc structDef unfolding TypeSafe_def compPointers_def by blast

          then have cmpStoPtr2:"(if TypedStoSubpref l x2 struct then CompStoType struct (STArray x t''') x2 l
             else if TypedStoSubpref x2 l (STArray x t''') then CompStoType (STArray x t''') struct l x2 else True)"
            using 10(3) lInDen inDen Storeloc structDef t''Def sameStack by simp

          have SConx4Old:"SCon struct x2 (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using Storeloc inDen 2(1) sameStack structDef
            by fastforce

          have "SCon struct x2 (Storage st' (Address env))"
          proof(cases "TypedStoSubpref l x2 struct")
            case True
            then have "CompStoType struct (STArray x t''') x2 l" using cmpStoPtr2 by simp
            then show ?thesis using SCondest2 SConx4Old a35 t''Def TypedStoSubpref_shared_parent_related SCon_sub_imps_Parent
              by blast

          next
            case f1:False
            then show ?thesis
            proof(cases "TypedStoSubpref x2 l (STArray x t''')")
              case True
              then have "CompStoType t' struct l x2 " using cmpStoPtr2 f1 t''Def by simp
              then show ?thesis using SCondest3 SCon_imps_sublocs by blast
            next
              case False
              have notSame:"x2 \<noteq> l" using False by auto
              have k7:"\<forall>locs. TypedStoSubpref locs x2 struct \<longrightarrow> locs \<noteq> l " using f1 by blast
              have k8:"\<forall>locs. TypedStoSubpref locs l (STArray x t''') \<longrightarrow> locs \<noteq> x2" using False by auto
              show ?thesis using sublocs_nonchanged_SCon[OF f1 a35 SConx4Old False] by blast
            qed
          qed
          then show ?thesis by simp
        next
          case sub2:(2 l''' t)
          have cmpStoPtr:"(
              (type.Storage struct, Storeloc x2) |\<in>| fmran (Denvalue env) \<and>
              (type.Storage t, Storeloc l''') |\<in>| fmran (Denvalue env) )
               \<longrightarrow>
              (if TypedStoSubpref l''' x2 struct then CompStoType struct t x2 l'''
               else if TypedStoSubpref x2 l''' t then CompStoType t struct l''' x2 else True)"
            using 2(1) 10(3) inDen Storeloc structDef unfolding TypeSafe_def compPointers_def by blast

          then have cmpStoPtr2:"(if TypedStoSubpref l''' x2 struct then CompStoType struct t x2 l'''
               else if TypedStoSubpref x2 l''' t then CompStoType t struct l''' x2 else True)"
            using 10(3) sub2 inDen Storeloc structDef t''Def sameStack by auto

          have SConx4Old:"SCon struct x2 (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using Storeloc inDen 2(1) sameStack structDef
            by fastforce
          have scl''':"SCon t l''' (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using sub2 by fastforce

          have "SCon struct x2 (Storage st' (Address env))"
          proof(cases "TypedStoSubpref l''' x2 struct")
            case True
            then have "CompStoType struct t x2 l'''" using cmpStoPtr2 by simp
            then have "CompStoType struct (STArray x t''') x2 l" using sub2
              using CompStoType_trns t''Def by blast
            then show ?thesis using SCondest2 SConx4Old a35 t''Def TypedStoSubpref_shared_parent_related SCon_sub_imps_Parent
              by blast
          next
            case f1:False
            then show ?thesis
            proof(cases "TypedStoSubpref x2 l''' t")
              case True
              then have "l''' \<noteq> x2" using f1
                using TypedStoSubpref_sameLoc by auto
              then show ?thesis
              proof(cases "l = x2")
                case t5:True
                then have " CompStoType t struct l''' x2" using cmpStoPtr2 f1 t''Def True by simp
                moreover have "CompStoType t t' l''' x2" using t5 sub2 by auto
                ultimately have "t' = struct" using CompStoType_sameLocs_sameType
                  by simp
                then show ?thesis using SCondest3 SCon_imps_sublocs t5 by simp
              next
                case False
                then have " CompStoType t struct l''' x2" using cmpStoPtr2 f1 t''Def True by simp
                then show ?thesis
                proof(cases "CompStoType t' struct l x2 ")
                  case True
                  then show ?thesis
                    using SCon_imps_sublocs SCondest3 by blast
                next
                  case False
                  then show ?thesis
                    using SCon_imps_sublocs SCon_sub_imps_Parent SCondest2 \<open>CompStoType t struct l''' x2\<close> a35 scl''' sub2(2) t''Def by blast
                qed
              qed
            next
              case False
              then have asm10:"\<not> TypedStoSubpref l x2 struct" using NotRelatedPrnt_imps_notRelatedChild[OF False f1 ] sub2 by blast
              then have asm20:"\<not> TypedStoSubpref x2 l t'" using sub2 NotReachablePrnt_imps_notReachableChild False f1 by blast
              have notSame:"x2 \<noteq> l" using False sub2 by blast
              have k7:"\<forall>locs. TypedStoSubpref locs x2 struct \<longrightarrow> locs \<noteq> l " using f1 sub2 asm10 asm20 by blast
              have k8:"\<forall>locs. TypedStoSubpref locs l (STArray x t''') \<longrightarrow> locs \<noteq> x2" using False sub2 t''Def asm10 asm20 by blast
              show ?thesis using sublocs_nonchanged_SCon[OF _ a35 SConx4Old] asm10 asm20 t''Def by blast
            qed
          qed

          then show ?thesis by simp
        next
          case sub3:(3 l''' t l'''')
          have cmpStoPtr:"(
              (type.Storage struct, Storeloc x2) |\<in>| fmran (Denvalue env) \<and>
              (type.Storage t, Stackloc l'''') |\<in>| fmran (Denvalue env) \<and>
               accessStore l'''' (Stack st) = Some (KStoptr l'''))
               \<longrightarrow>
              (if TypedStoSubpref l''' x2 struct then CompStoType struct t x2 l'''
               else if TypedStoSubpref x2 l''' t then CompStoType t struct l''' x2 else True)"
            using 2(1) 10(3) inDen Storeloc structDef unfolding TypeSafe_def compPointers_def by blast

          then have cmpStoPtr2:"(if TypedStoSubpref l''' x2 struct then CompStoType struct t x2 l'''
               else if TypedStoSubpref x2 l''' t then CompStoType t struct l''' x2 else True)"
            using 10(3) sub3 inDen Storeloc structDef t''Def sameStack by auto

          have SConx4Old:"SCon struct x2 (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using Storeloc inDen 2(1) sameStack structDef
            by fastforce
          have scl''':"SCon t l''' (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using sub3 by fastforce

          have "SCon struct x2 (Storage st' (Address env))"
          proof(cases "TypedStoSubpref l''' x2 struct")
            case True
            then have "CompStoType struct t x2 l'''" using cmpStoPtr2 by simp
            then have "CompStoType struct (STArray x t''') x2 l" using sub3
              using CompStoType_trns t''Def by blast
            then show ?thesis using SCondest2 SConx4Old a35 t''Def TypedStoSubpref_shared_parent_related SCon_sub_imps_Parent
              by blast
          next
            case f1:False
            then show ?thesis
            proof(cases "TypedStoSubpref x2 l''' t")
              case True
              then have "l''' \<noteq> x2" using f1
                using TypedStoSubpref_sameLoc by auto
              then show ?thesis
              proof(cases "l = x2")
                case t5:True
                then have " CompStoType t struct l''' x2" using cmpStoPtr2 f1 t''Def True by simp
                moreover have "CompStoType t t' l''' x2" using t5 sub3 by auto
                ultimately have "t' = struct" using CompStoType_sameLocs_sameType
                  by simp
                then show ?thesis using SCondest3 SCon_imps_sublocs t5 by simp
              next
                case False
                then have " CompStoType t struct l''' x2" using cmpStoPtr2 f1 t''Def True by simp
                then show ?thesis
                proof(cases "CompStoType t' struct l x2 ")
                  case True
                  then show ?thesis
                    using SCon_imps_sublocs SCondest3 by blast
                next
                  case False
                  then show ?thesis
                    using SCon_imps_sublocs SCon_sub_imps_Parent SCondest2 \<open>CompStoType t struct l''' x2\<close> a35 scl''' sub3(3) t''Def by blast
                qed
              qed
            next
              case False
              then have asm10:"\<not> TypedStoSubpref l x2 struct" using NotRelatedPrnt_imps_notRelatedChild[OF False f1 ] sub3 by blast
              then have asm20:"\<not> TypedStoSubpref x2 l t'" using sub3 NotReachablePrnt_imps_notReachableChild False f1 by blast
              have notSame:"x2 \<noteq> l" using False sub3 by blast
              have k7:"\<forall>locs. TypedStoSubpref locs x2 struct \<longrightarrow> locs \<noteq> l " using f1 sub3 asm10 asm20 by blast
              have k8:"\<forall>locs. TypedStoSubpref locs l (STArray x t''') \<longrightarrow> locs \<noteq> x2" using False sub3 t''Def asm10 asm20 by blast
              show ?thesis using sublocs_nonchanged_SCon[OF _ a35 SConx4Old] asm10 asm20 t''Def by blast
            qed
          qed
          then show ?thesis by simp
        qed
        then show ?thesis using Storeloc inDen 2(1) sameStack Storeloc structDef by simp
      qed
    qed
    then have "typeCompat (Denvalue env) (Stack st) (Memory st') (Storage st' (Address env)) cd " using sameStack by simp
  next
    have "Accounts st'= Accounts st" using 10 by auto
    then show "fullyInitialised env (Accounts st') (Stack st')" using 2(3) 10 unfolding fullyInitialised_def by auto
  next
    have cc0:"\<forall>l ptr_loc. accessStore l (Stack st') = Some (KMemptr ptr_loc) \<longrightarrow> accessStore l (Stack st) = Some (KMemptr ptr_loc)"
      using 10(5) unfolding updateStore_def accessStore_def by auto
    show "denvalueTypeCorrectness env (Stack st') (Memory st')"

      unfolding denvalueTypeCorrectness_def
    proof intros
      fix t l ptr_loc sub_loc
      assume "(type.Memory t, Stackloc l) |\<in>| fmran (Denvalue env) \<and>
     accessStore l (Stack st') = Some (KMemptr ptr_loc)"
      then have "(case t of
      MTArray len arr \<Rightarrow>
         (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr)
       | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st) = Some (MTValue val))"
        using 2(1) unfolding TypeSafe_def denvalueTypeCorrectness_def using cc0 by blast
      moreover have "Memory st = Memory st'" using 10(5) by simp
      ultimately show "case t of
     MTArray len arr \<Rightarrow>
      (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr)
     | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st') = Some (MTValue val)"
        by metis
    qed
  next
    show "subPrefixStructuralConsistency (Memory st')" using 2(1) unfolding TypeSafe_def using 10(5) by auto
  next
    show "SomeValSomeTyp (Memory st')" using 2(1) unfolding TypeSafe_def using 10(5) by auto
  next
    show "\<And>locs t. accessTypeStore locs (Memory st) = Some t \<Longrightarrow> accessTypeStore locs (Memory st') = Some t "
      using 2(1) unfolding TypeSafe_def using 10(5) by auto
  next
    show "\<And>locs v. accessStore locs (Memory st) = Some (MPointer v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MPointer v')"
      using 10(5) by simp
  next
    show "\<And>locs v. accessStore locs (Memory st) = Some (MValue v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MValue v')"
      using 10(5) by simp
  next
    show " \<And>i loc. i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<Longrightarrow> accessStore loc
        (Memory st) = None \<Longrightarrow> accessStore loc (Memory st') = None"
      using 10(5) by simp
  next
    show "Toploc (Memory st) \<le> Toploc (Memory st')" using 10(5)by simp
  qed
qed

text \<open>Assignment case 11: a memory array assigned to a memory location: the location is updated to point to the same array.\<close>

lemma TypeSafe_Assign_11:
  assumes "TypeSafe env (Accounts st) (Stack st) (Memory st) (Storage st) cd"
    and "stmt (ASSIGN lv ex) env cd st = Normal ((), st')"
    and "fullyInitialised env (Accounts st) (Stack st)"
    and "expr ex env cd (st\<lparr>state.Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>) (state.Gas st - costs (ASSIGN lv
        ex) env cd st) = Normal ((KMemptr p, type.Memory (MTArray x t)), g)"
    and "lexp lv env cd (st\<lparr>state.Gas := g\<rparr>) g = Normal((LMemloc l, type.Memory t'),g')"
    and "t' = MTArray x t"
    and "st' = st\<lparr>state.Gas := g', Memory := updateStore l (MPointer p) (Memory st)\<rparr>"
  shows "StateInvariant env st st' cd"
proof -
  let ?case = "StateInvariant env st st' cd"
  note 2 = assms(1-3)
  note 11 = assms(4-7)
  have temp:"TypeSafe env (Accounts (st\<lparr>Gas := g\<rparr>)) (Stack (st\<lparr>Gas := g\<rparr>)) (Memory (st\<lparr>Gas := g\<rparr>)) (Storage (st\<lparr>Gas := g\<rparr>)) cd"
    using 2(1) by simp
  have ttt:"fullyInitialised env (Accounts (st\<lparr>Gas := g\<rparr>)) (Stack (st\<lparr>Gas := g\<rparr>))" using 2(3) unfolding fullyInitialised_def by simp
  then show ?thesis
  proof(cases rule:lexpIndexMem[OF 11(2) temp ttt])
    case lInfo:(1 x21 x22 tp tParent l' l'' prnt len' arr' i)
    have sameStack:"(Stack st') = Stack st" using 11 unfolding accessStore_def updateStore_def by auto
    have sameStorage:"Storage st' = Storage st " using 11 by auto
    have accL:"accessStore l (Memory st') = Some (MPointer p)" using 11(4) by auto
    have nonLocChanged:"\<forall>locs. locs \<noteq> l \<longrightarrow> accessStore locs (Memory st') = accessStore locs (Memory st)"
      using 11 unfolding updateStore_def accessStore_def by simp

    have MConsrc:"MCon (MTArray x t) (Memory (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)) (extractValueType (KMemptr p)) \<and>
      (\<exists>xx. KMemptr p = KMemptr xx) \<and>
      (\<exists>stloc tp'' pa.
          (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue env) \<and>
          accessStore stloc (Stack (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)) = Some (KMemptr pa) \<and>
          (tp'' = (MTArray x t) \<and> KMemptr p = KMemptr pa \<or>
           (\<exists>len arr.
               extractValueType (KMemptr p) \<noteq> pa \<and>
               tp'' = MTArray len arr \<and> CompMemType (Memory (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)) len arr (MTArray x t) pa (extractValueType (KMemptr p)))))"
      using 2(1) 11(1) exprTypeconInduct(3)[of ex env cd "(st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)"
          "(state.Gas st - costs (ASSIGN lv ex) env cd st)" "KMemptr p" "type.Memory (MTArray x t)" g]
      using 2(3) unfolding fullyInitialised_def
      by (auto split:type.splits if_splits )


    then obtain pParent pParentT pParentPtr where
      pOrigin:"MCon (MTArray x t) (Memory (st)) (extractValueType (KMemptr p)) \<and>(type.Memory pParentT, Stackloc pParent) |\<in>| fmran (Denvalue env) \<and>
          accessStore pParent (Stack (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)) = Some (KMemptr pParentPtr) \<and>
          (pParentT = (MTArray x t) \<and> KMemptr p = KMemptr pParentPtr \<or>
           (\<exists>len arr.
               extractValueType (KMemptr p) \<noteq> pParentPtr \<and>
               pParentT = MTArray len arr \<and> CompMemType (Memory (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd
                   st\<rparr>)) len arr (MTArray x t) pParentPtr (extractValueType (KMemptr p))))"
      by force
    then have l:"MCon pParentT (Memory st) pParentPtr" using sameMemTSafe[OF 2(1)] by auto

    have pTAccessOld:"(\<forall>i<x. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some t)"
    proof(cases "pParentT = (MTArray x t) \<and> KMemptr p = KMemptr pParentPtr")
      case True
      then show ?thesis using 2(1) unfolding TypeSafe_def denvalueTypeCorrectness_def
        using pOrigin by fastforce
    next
      case False
      then obtain l1 a1 where l1Def:"(p \<noteq> pParentPtr \<and> pParentT = MTArray l1 a1
                  \<and> CompMemType (Memory st) l1 a1 (MTArray x t) pParentPtr p)"
        using pOrigin by auto
      then have prntT:" \<forall>i<l1. accessTypeStore (hash pParentPtr (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some a1"
        using pOrigin using 2(1) unfolding TypeSafe_def denvalueTypeCorrectness_def
        by fastforce
      have subPref:"subPrefixStructuralConsistency (Memory st)"
        using 2(1) unfolding TypeSafe_def by blast
      then show ?thesis using CompMemTypeSubIndexes[OF _ subPref _ prntT] l1Def
        using l by blast
    qed


    obtain len subT where tParentType:"tParent = MTArray len subT" using lInfo by blast
    then obtain p'' where lOrigin:"accessStore l (Memory (st)) = Some (MPointer p'')"
        and compType:"CompMemType (Memory (st\<lparr>Gas := g\<rparr>)) len subT (MTArray x t) l'' p''"
        and lsublocs:"l = hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<and> i < len' \<and> arr' = (MTArray x t) \<and> MCon (MTArray len' arr') (Memory (st)) prnt"
        and lsublocs3:"(prnt = l'' \<and> len = len' \<and> arr' = subT \<or> CompMemType (Memory (st)) len subT (MTArray len' arr') l'' prnt)"
      using lInfo 11(3) by force
    then have lsublocs2:" CompMemType (Memory (st)) len' arr' (MTArray x t) prnt p''"
      using 11(3) CompMemType.simps(2) by blast
    then have bb9:"\<forall>subT subloc. CompMemType (Memory (st)) len' arr' subT prnt subloc \<and> subloc = p''
                                \<longrightarrow> subT = (MTArray x t)"
      using CompMemTypeSameLocsSameType lsublocs by blast

    have mconPrnt:"MCon (MTArray len' (MTArray x t)) (Memory st) prnt" using lsublocs by auto
    have ldef:"l = hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<and> i < len'" using lsublocs by auto

    have t6:"(type.Memory tParent, Stackloc l') |\<in>| fmran (Denvalue env)" using lInfo by blast
    have t7:" MCon (MTArray len subT) (Memory (st)) l''" using lInfo
      using tParentType by auto
    then have mconlOld:"MCon (MTArray x t) (Memory st) p''" using 11(3) lInfo lOrigin by auto

    have mcP:"MCon (MTArray x t) (Memory st) p" using MConsrc by force
    have compP:"\<not>CompMemType (Memory (st)) x t (MTArray len' (MTArray x t)) p prnt"
      using MCon_subTypes_imps_noPrnt mcP mconPrnt
      by simp
    have pNotPrnt:"p \<noteq> prnt" using mcP mconPrnt nonLocChanged
      using MConSubTypes CompMemJustType.simps(2) by blast
    have pSubs:"TypedMemSubPrefPtrs (Memory st) len' (MTArray x t) prnt p \<longrightarrow> (\<exists>i'. accessStore (hash prnt
        (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (Memory st) = Some (MPointer p) \<and> i'<len')"
    proof intros
      assume in1:"TypedMemSubPrefPtrs (Memory st) len' (MTArray x t) prnt p"
      then obtain i2 l2 where i2Def: "i2<len' \<and> accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) (Memory st) = Some
          (MPointer l2) \<and> (l2 = p \<or> TypedMemSubPrefPtrs (Memory st) x t l2 p)"
        unfolding TypedMemSubPrefPtrs.simps by blast
      show "\<exists>i'. accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (Memory st) = Some (MPointer p) \<and> i' < len'"
      proof(cases "l2 = p")
        case True
        then show ?thesis using i2Def by auto
      next
        case False
        then have in2:"TypedMemSubPrefPtrs (Memory st) x t l2 p" using i2Def by simp
        have in3:"\<forall>ta. CompMemJustType t ta \<longrightarrow> \<not> MCon ta (Memory st) p" using MConSubTypes[OF mcP] by blast
        have "MCon (MTArray x t) (Memory st) l2" using i2Def mconPrnt
          using MCon_imps_sub_Mcon by blast

        then show ?thesis using in3 in2
        proof(induction t arbitrary:l2 x)
          case (MTArray x1 t)
          obtain i3 l3 where i3Def:"i3<x \<and> accessStore (hash l2 (ShowL\<^sub>n\<^sub>a\<^sub>t i3)) (Memory st) = Some (MPointer l3)
                                    \<and> (l3 = p \<or> TypedMemSubPrefPtrs (Memory st) x1 t l3 p)"
            using MTArray.prems(3) unfolding TypedMemSubPrefPtrs.simps by auto
          then have mcL3:"MCon (MTArray x1 t) (Memory st) l3" using MTArray.prems(1)
            using MconSameTypeSameAccessWithTyping by blast
          then have notP:"l3 \<noteq> p" using MTArray.prems(3)
            using MConSubTypes MTArray.prems(2) CompMemJustType.simps(2) by blast
          have "\<forall>taa. CompMemJustType t taa \<longrightarrow> \<not> MCon taa (Memory st) p" using MTArray.prems by simp
          moreover have "TypedMemSubPrefPtrs (Memory st) x1 t l3 p" using notP i3Def by simp
          ultimately show ?case using MTArray.IH mcL3 by blast
        next
          case (MTValue x')
          then show ?case
            by (metis CompTypeRemainsMCon TypedMemSubPrefPtrs.simps(1) CompMemJustType.simps(1) CompMemType.simps(1))
        qed
      qed
    qed

    have p''ToPrnt:"\<not>TypedMemSubPrefPtrs (Memory st) x t p'' prnt"
      by (meson CompMemType_imps_CompMemJustType CompMemType_imps_TypedMemSubPrefPtrs CompTypeRemainsMCon TypedMemSubPrefOneWay lsublocs lsublocs2)
    moreover have p''notprnt:"p'' \<noteq>prnt" using lsublocs2
      using CompMemType_imps_TypedMemSubPrefPtrs TypedMemSubPrefPtrs_imps_notsame lsublocs by blast
    ultimately have mcP''New:"MCon (MTArray x t) (Memory st') p''" using mconlOld limitedMemoryChange[of "Memory st" x t p'' prnt i ] nonLocChanged 11 ldef by fastforce

    have mcPrnt:"\<exists>t''. MCon t'' (Memory st) prnt \<and> CompMemJustType t'' (MTArray x t) \<and> t'' \<noteq> (MTArray x t)" using mconPrnt by fastforce
    have asf:"\<not>TypedMemSubPrefPtrs (Memory st) x t p prnt"
    proof
      assume in1:"TypedMemSubPrefPtrs (Memory st) x t p prnt"
      then show False using mcP mcPrnt
      proof(induction t arbitrary:x p)
        case (MTArray x1 t)
        then obtain i2 l2 where i2Def: "i2<x \<and> accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) (Memory st) = Some (MPointer l2)
                                           \<and> (l2 = prnt \<or> TypedMemSubPrefPtrs (Memory st) x1 t l2 prnt)"
          unfolding TypedMemSubPrefPtrs.simps by blast
        then have mcl2:"MCon (MTArray x1 t) (Memory st) l2" using MTArray.prems(2)
          using MCon_imps_sub_Mcon by blast
        then show ?case
        proof(cases "l2 = prnt")
          case True
          then have "MCon (MTArray x1 t) (Memory st) prnt" using mcl2 by simp
          then show ?thesis
          proof -
            obtain t'' where t'': "MCon t'' (Memory st) prnt" "CompMemJustType t'' (MTArray x (MTArray x1 t))"
                "t'' \<noteq> MTArray x (MTArray x1 t)"
              using MTArray.prems(3) by blast
            then have "CompMemJustType t'' (MTArray x1 t)"
              using CompMemTypes_asc CompMemJustType_refl by fastforce
            then have "t'' = MTArray x1 t"
              using MCon_CompMemJustType_unique[OF CompMemJustType_refl _ t''(1)] \<open>MCon (MTArray x1 t) (Memory st) prnt\<close> by blast
            then show False
              using t''(2,3) reversible_CompMemJustType_imps_same CompMemJustType_refl by fastforce
          qed
        next
          case False
          then have "TypedMemSubPrefPtrs (Memory st) x1 t l2 prnt" using i2Def by simp
          then show ?thesis using MTArray.IH[OF _ mcl2] MTArray.prems(3)
            by (metis CompMemTypes_asc reversible_CompMemJustType_imps_same CompMemJustType.simps(2))
        qed
      next
        case (MTValue x')
        then have "\<exists>i<x. hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i) = prnt" unfolding TypedMemSubPrefPtrs.simps by blast
        then show ?case using MTValue unfolding MCon.simps
          using lsublocs by fastforce
      qed
    qed

    have mcPNew:"MCon (MTArray x t) (Memory st') p" using mcP asf pNotPrnt
    proof(induction t arbitrary: x p)
      case (MTArray x1 t)
      then have xnotzero:"x \<noteq> 0" unfolding MCon.simps by simp
      have "\<forall>i<x. (case accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') of None \<Rightarrow> False
             | Some (MValue val) \<Rightarrow> (case MTArray x1 t of MTArray l a \<Rightarrow> False
                                | MTValue typ \<Rightarrow> MCon (MTArray x1 t) (Memory st') (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
             | Some (MPointer loc2) \<Rightarrow> (case MTArray x1 t of MTArray len' arr' \<Rightarrow> MCon (MTArray x1 t) (Memory st') loc2 | MTValue Types \<Rightarrow> False)) \<and>
            ((\<exists>p'. accessStore p (Memory st') = Some (MPointer p')) \<or> accessStore p (Memory st') = None)"
      proof(intros)
        fix i2 assume i2Def:"i2<x"
        have "(hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) \<noteq> l"
        proof
          assume in1':"hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i2) = l"
          then have "p = prnt" using ldef ShowLNatDot
            using hash_injective by blast
          then show False using MTArray.prems(3) by simp
        qed
        then have sameAccess:"accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) (Memory st') = accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) (Memory st)" using nonLocChanged by simp
        then obtain p2 where p2Def: "accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) (Memory st') = Some (MPointer p2) \<and> MCon (MTArray x1 t) (Memory st) p2" using i2Def
          using MTArray.prems by (metis MConArrayPointers MCon_imps_sub_Mcon bot_nat_0.not_eq_extremum xnotzero)
        then have "\<not> TypedMemSubPrefPtrs (Memory st) x1 t p2 prnt" using MTArray.prems
          using i2Def sameAccess by fastforce
        moreover have "p2 \<noteq> prnt" using MTArray.prems p2Def i2Def
          by (simp add: sameAccess)
        ultimately have "MCon (MTArray x1 t) (Memory st') p2" using MTArray.IH[of x1 p2] p2Def MTArray.prems by blast
        then show "case accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) (Memory st') of None \<Rightarrow> False
     | Some (MValue val) \<Rightarrow> (case MTArray x1 t of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTArray x1 t) (Memory st') (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i2)))
     | Some (MPointer loc2) \<Rightarrow> (case MTArray x1 t of MTArray len' arr' \<Rightarrow> MCon (MTArray x1 t) (Memory st') loc2 | MTValue Types \<Rightarrow> False)"
          using p2Def by simp
        show "(\<exists>p'. accessStore p (Memory st') = Some (MPointer p')) \<or> accessStore p (Memory st') = None"
        proof(cases "p = l")
          case True
          then show ?thesis using 11 by simp
        next
          case False
          then show ?thesis using nonLocChanged using MTArray.prems(1) unfolding MCon.simps
            using i2Def sameAccess by simp
        qed
      qed
      then show ?case using MCon.simps(2)[of x "(MTArray x1 t)" "Memory st'" p ] xnotzero
        by simp
    next
      case (MTValue x')
      then have xnotzero:"x \<noteq> 0" unfolding MCon.simps by simp
      have "\<forall>i<x. (case accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') of None \<Rightarrow> False
            | Some (MValue val) \<Rightarrow>
                (case MTValue x' of MTArray l a \<Rightarrow> False
                | MTValue typ \<Rightarrow> (case accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') of None
                    \<Rightarrow> False | Some (MValue xa) \<Rightarrow> typeCon x' xa | Some (MPointer t) \<Rightarrow> False))
            | Some (MPointer loc2) \<Rightarrow>
                (case MTValue x' of MTArray len' arr' \<Rightarrow> (case accessStore loc2 (Memory st') of None \<Rightarrow> False | Some
                    (MValue xa) \<Rightarrow> typeCon x' xa | Some (MPointer t) \<Rightarrow> False)
                | MTValue Types \<Rightarrow> False))\<and>
           ((\<exists>p'. accessStore p (Memory st') = Some (MPointer p')) \<or> accessStore p (Memory st') = None)"
      proof(intros)
        fix i2 assume i2Def:"i2<x"
        then have "(hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) \<noteq> l" using ldef
          by (metis MCon_sub_MTVal_imps_val MTValue.prems(1) memoryvalue.distinct(1) lOrigin option.inject)
        then have sameAccess:" accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) (Memory st') = accessStore (hash p
            (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) (Memory st)" using nonLocChanged by simp
        then show "case accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) (Memory st') of None \<Rightarrow> False
     | Some (MValue val) \<Rightarrow>
         (case MTValue x' of MTArray l a \<Rightarrow> False
         | MTValue typ \<Rightarrow> (case accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) (Memory st') of None \<Rightarrow>
             False | Some (MValue xa) \<Rightarrow> typeCon x' xa | Some (MPointer t) \<Rightarrow> False))
     | Some (MPointer loc2) \<Rightarrow>
         (case MTValue x' of MTArray len' arr' \<Rightarrow> (case accessStore loc2 (Memory st') of None \<Rightarrow> False | Some
             (MValue xa) \<Rightarrow> typeCon x' xa | Some (MPointer t) \<Rightarrow> False)
         | MTValue Types \<Rightarrow> False)" using MTValue(1) i2Def mcon_accessStore xnotzero by (auto split:option.splits memoryvalue.splits mtypes.splits)
        show "(\<exists>p'. accessStore p (Memory st') = Some (MPointer p')) \<or> accessStore p (Memory st') = None"
        proof(cases "p = l")
          case True
          then show ?thesis using 11 by simp
        next
          case False
          then show ?thesis using nonLocChanged using MTValue(1) unfolding MCon.simps
            using i2Def sameAccess by simp
        qed
      qed
      then show ?case unfolding MCon.simps using xnotzero
        by simp
    qed

    have mcPrntNew:"MCon (MTArray len' (MTArray x t)) (Memory st') prnt"
    proof -
      have lenNotZero:"len' \<noteq> 0" using lsublocs by auto
      have prntNotL:"prnt \<noteq> l" using ldef
        by (metis hash_inequality)
      then have p2:"(\<exists>p. accessStore prnt (Memory st') = Some (MPointer p)) \<or> accessStore prnt (Memory st') = None"
        using mconPrnt lenNotZero nonLocChanged by simp
      have "\<forall>i<len'.
         (case accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') of None \<Rightarrow> False
          | Some (MValue val) \<Rightarrow> (case MTArray x t of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTArray
              x t) (Memory st') (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
          | Some (MPointer loc2) \<Rightarrow> (case MTArray x t of MTArray len' arr' \<Rightarrow> MCon (MTArray x t) (Memory st') loc2 | MTValue Types \<Rightarrow> False))"
      proof(intros)
        fix i1 assume in1:"i1<len'"
        show "case accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) (Memory st') of None \<Rightarrow> False
       | Some (MValue val) \<Rightarrow> (case MTArray x t of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTArray x
           t) (Memory st') (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i1)))
       | Some (MPointer loc2) \<Rightarrow> (case MTArray x t of MTArray len' arr' \<Rightarrow> MCon (MTArray x t) (Memory st') loc2 | MTValue Types \<Rightarrow> False)"
        proof(cases "i1 = i")
          case True
          then have "(hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) = l" using ldef by simp
          then have "accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) (Memory st') = Some(MPointer p)" using 11 by simp
          then show ?thesis using mcPNew by simp
        next
          case False
          then have "accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) (Memory st') = accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) (Memory st)" using ldef nonLocChanged in1
            by (metis Read_Show_nat'_id hash_never_equal_suffix)
          then obtain ptr where ptrDef:"accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) (Memory st) = Some (MPointer ptr)" using in1
            using MConArrayPointers lsublocs by blast
          then have ptrMC:"MCon (MTArray x t) (Memory st) ptr" using in1 mconPrnt
            using MCon_imps_sub_Mcon by blast
          moreover have sub2:"\<forall>p ta. MCon ta (Memory st) p \<and> CompMemType (Memory st) len' (MTArray x t) ta prnt p \<longrightarrow> p \<noteq> prnt"
            using MConPtrsMustBeSubLocs_CompMemType[OF mconPrnt] by auto
          moreover have ptrPrnt:"CompMemType (Memory st) len' (MTArray x t) (MTArray x t) prnt ptr" using ptrDef in1 by auto
          ultimately have prtNotPrnt:"ptr \<noteq> prnt" by blast
          have sub3:"\<forall>p ta. CompMemType (Memory st) x t ta ptr p \<longrightarrow> p \<noteq> prnt" using ptrPrnt sub2 ptrMC
            by (metis CompMemType_imps_CompMemJustType CompTypeRemainsMCon MConSubTypes mconPrnt)
          have "MCon (MTArray x t) (Memory st') ptr" using ptrMC sub3 prtNotPrnt
          proof (induction t arbitrary:x ptr)
            case (MTArray x1 t)
            then have xnotZero:"x \<noteq> 0" by fastforce
            have "\<forall>i<x. (case accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') of None \<Rightarrow> False
               | Some (MValue val) \<Rightarrow> (case MTArray x1 t of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon
                   (MTArray x1 t) (Memory st') (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
               | Some (MPointer loc2) \<Rightarrow> (case MTArray x1 t of MTArray len' arr' \<Rightarrow> MCon (MTArray x1 t) (Memory st') loc2 | MTValue Types \<Rightarrow> False)) \<and>
              ((\<exists>p. accessStore ptr (Memory st') = Some (MPointer p)) \<or> accessStore ptr (Memory st') = None)"
            proof intros
              fix i2 assume i2Def:"i2<x"
              have "ptr \<noteq> prnt" using MTArray.prems by simp
              then have notL:"(hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) \<noteq> l" using ldef ShowLNatDot
                using hash_injective by blast
              then have sameAccess:"accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) (Memory st') = accessStore (hash ptr
                  (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) (Memory st)" using nonLocChanged by auto
              then obtain ptr2 where ptr2Def: "accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) (Memory st') = Some (MPointer ptr2) \<and> MCon (MTArray x1 t) (Memory st) ptr2"
                using MTArray.prems(1) i2Def
                by (metis MConArrayPointers MCon_imps_sub_Mcon bot_nat_0.not_eq_extremum xnotZero)
              moreover have "\<forall>p taa. CompMemType (Memory st) x1 t taa ptr2 p \<longrightarrow> p \<noteq> prnt " using MTArray.prems ptr2Def i2Def
                by (metis sameAccess CompMemType.simps(2))
              moreover have "ptr2 \<noteq> prnt" using MTArray.prems ptr2Def i2Def
                by (metis sameAccess CompMemType.simps(2))
              ultimately show "case accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) (Memory st') of None \<Rightarrow> False
                    | Some (MValue val) \<Rightarrow> (case MTArray x1 t of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow>
                        MCon (MTArray x1 t) (Memory st') (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i2)))
                    | Some (MPointer loc2) \<Rightarrow> (case MTArray x1 t of MTArray len' arr' \<Rightarrow> MCon (MTArray x1 t) (Memory st') loc2 | MTValue Types \<Rightarrow> False)"
                using MTArray.IH[of x1 ptr2] using ptr2Def by fastforce
              show " (\<exists>p. accessStore ptr (Memory st') = Some (MPointer p)) \<or> accessStore ptr (Memory st') = None "
              proof(cases "ptr = l")
                case True
                then show ?thesis using 11 by simp
              next
                case False
                then show ?thesis using nonLocChanged MTArray.prems(1)
                  using i2Def by fastforce
              qed
            qed
            then show ?case using MCon.simps(2)[of x "MTArray x1 t" "Memory st'" ptr] using xnotZero by simp
          next
            case (MTValue x')
            then have xnotZero:"x \<noteq> 0" by fastforce
            have "\<forall>i<x. (case accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') of None \<Rightarrow> False
               | Some (MValue val) \<Rightarrow> (case MTValue x' of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon
                   (MTValue x') (Memory st') (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
               | Some (MPointer loc2) \<Rightarrow> (case MTValue x' of MTArray len' arr' \<Rightarrow> MCon (MTValue x') (Memory st') loc2 | MTValue Types \<Rightarrow> False)) \<and>
              ((\<exists>p. accessStore ptr (Memory st') = Some (MPointer p)) \<or> accessStore ptr (Memory st') = None)"
            proof(intros)
              fix i2 assume i2Def:"i2<x"
              have "(hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) \<noteq> l" using MTValue
                by (metis MCon_sub_MTVal_imps_val memoryvalue.distinct(1) i2Def lOrigin option.inject)
              then have "accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) (Memory st') = accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) (Memory st)" using nonLocChanged by simp
              then show "case accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) (Memory st') of None \<Rightarrow> False
       | Some (MValue val) \<Rightarrow> (case MTValue x' of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTValue x') (Memory st') (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i2)))
       | Some (MPointer loc2) \<Rightarrow> (case MTValue x' of MTArray len' arr' \<Rightarrow> MCon (MTValue x') (Memory st') loc2 | MTValue Types \<Rightarrow> False)"
                using i2Def MTValue
                by (metis (lifting) CompTypeRemainsMCon mtypes.distinct(1) mtypes.simps(6) memoryvalue.simps(5) Option.option.simps(5) linorder_less_linear mcon_accessStore not_less_zero
                    CompMemType.simps(1) MCon.simps(1))
              show "(\<exists>p. accessStore ptr (Memory st') = Some (MPointer p)) \<or> accessStore ptr (Memory st') = None"
              proof(cases "ptr = l")
                case True
                then show ?thesis using 11 by simp
              next
                case False
                then show ?thesis using nonLocChanged MTValue i2Def by auto
              qed
            qed
            then show ?case using MCon.simps(2)[of x "MTValue x'" "Memory st'" ptr] xnotZero by simp
          qed
          then show ?thesis
            by (simp add: \<open>accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) (Memory st') = accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) (Memory st)\<close> ptrDef)
        qed
      qed

      then show ?thesis using lenNotZero p2 by simp
    qed

    have compmemst':"\<forall>locs lens subTs. CompMemType (Memory st) lens subTs (MTArray len' arr') locs prnt
                          \<and> MCon (MTArray lens subTs) (Memory st) locs
                        \<longrightarrow> CompMemType (Memory (st')) lens subTs (MTArray len' arr') locs prnt"
    proof intros
      fix locs lens subTs
      assume asm1:"CompMemType (Memory st) lens subTs (MTArray len' arr') locs prnt \<and> MCon (MTArray lens subTs) (Memory st) locs"
      then have asm5:"CompMemType (Memory st) lens subTs (MTArray len' arr') locs prnt" by blast
      have asm6:"MCon (MTArray lens subTs) (Memory st) locs" using asm1 by blast

      have mconl'':"MCon (MTArray len subT) (Memory st) l''" using lInfo(5) tParentType by simp


      then have a10:"CompMemType (Memory st') lens subTs (MTArray len' arr') locs prnt" using asm6 asm5
      proof(induction subTs arbitrary: lens locs)
        case (MTArray x11 x12)

        then obtain iIn lIn where iInDef:"iIn<lens \<and> accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t iIn)) (Memory st) = Some (MPointer lIn)
                  \<and> (lIn = prnt \<and> MTArray x11 x12 = MTArray len' arr' \<or> CompMemType (Memory st) x11 x12 (MTArray len' arr') lIn prnt)"
          unfolding CompMemType.simps by blast
        have same2:" accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t iIn)) (Memory st) = accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t iIn)) (Memory st)"
          using MConArrayPointers MTArray.prems(2) bot_nat_0.not_eq_extremum iInDef le_eq_less_or_eq nonLocChanged not_less_zero option.discI by metis
        then have mcIn:"MCon (MTArray x11 x12) (Memory st) lIn" using same2 iInDef MTArray.prems
          by (metis MCon_imps_sub_Mcon)
        then show ?case
        proof(cases "lIn = prnt")
          case True
          have "prnt \<noteq> l" using ldef
            by (metis hash_inequality)
          moreover have "MTArray x11 x12 = MTArray len' arr'" using iInDef True
            by (metis CompMemType_imps_CompMemJustType MConSubTypes \<open>MCon (MTArray x11 x12) (Memory st) lIn\<close> lsublocs mconPrnt CompMemJustType.simps(2))
          ultimately show ?thesis using True
            by (metis MConPtrsMustBeSubLocs iInDef lsublocs nonLocChanged CompMemType.simps(2))
        next
          case False
          then have "CompMemType (Memory st) x11 x12 (MTArray len' arr') lIn prnt" using iInDef by blast
          then have cp:"CompMemType (Memory st') x11 x12 (MTArray len' arr') lIn prnt" using MTArray.IH[of x11 lIn] mcIn t7 by simp
          have "(hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t iIn)) \<noteq> l"
            by (metis CompMemType_imps_CompMemJustType CompMemTypes_asc MConSubTypes memoryvalue.inject(2) iInDef lOrigin lsublocs mcIn mconlOld option.inject
                CompMemJustType.simps(2))
          then have "accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t iIn)) (Memory st) = accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t iIn)) (Memory st')"
            by (simp add: nonLocChanged)
          then have "\<exists>i<lens. \<exists>l. accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some (MPointer l)
              \<and> (l = prnt \<and> MTArray x11 x12 = MTArray len' arr' \<or> CompMemType (Memory st') x11 x12 (MTArray len' arr') l prnt)"
            using False cp iInDef by metis
          then show ?thesis unfolding CompMemType.simps(2)
            using iInDef by blast
        qed
      next
        case (MTValue x2)
        then show ?case
          using compType by auto
      qed
      then show "CompMemType (Memory st') lens subTs (MTArray len' arr') locs prnt" by blast
    qed

    have "(type.Memory (MTArray len subT), Stackloc l') |\<in>| fmran (Denvalue env) \<and> accessStore l' (Stack st) = Some (KMemptr l'')"
      using lInfo(2,3,4) tParentType by simp


    have subPNew_imp_old:"\<forall>stl2. TypedMemSubPrefPtrs (Memory st') x t p stl2 \<longrightarrow> TypedMemSubPrefPtrs (Memory st) x t p stl2"
    proof intros
      fix stl2
      assume in1:"TypedMemSubPrefPtrs (Memory st') x t p stl2"
      then show "TypedMemSubPrefPtrs (Memory st) x t p stl2 " using asf pNotPrnt
      proof(induction t arbitrary:x p)
        case (MTArray x1 t)
        obtain iin lin where linDef: "iin<x \<and> accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) (Memory st') = Some (MPointer lin)
                                      \<and> (lin = stl2 \<or> TypedMemSubPrefPtrs (Memory st') x1 t lin stl2)"
          using MTArray.prems(1) unfolding TypedMemSubPrefPtrs.simps by blast
        have "(hash p (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) \<noteq> l" using MTArray.prems(3) ldef ShowLNatDot
          by (metis hash_injective)
        then have sameAccess:" accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) (Memory st') = accessStore (hash p
            (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) (Memory st)" using nonLocChanged by simp
        then show ?case
        proof(cases "lin = stl2")
          case True
          then show ?thesis using MTArray.prems sameAccess linDef by force
        next
          case False
          then have "TypedMemSubPrefPtrs (Memory st') x1 t lin stl2" using linDef by simp
          moreover have "\<not> TypedMemSubPrefPtrs (Memory st) x1 t lin prnt" using MTArray.prems(2) linDef
            using sameAccess by auto
          moreover have " lin \<noteq> prnt" using MTArray.prems linDef
            using sameAccess by auto
          ultimately have "TypedMemSubPrefPtrs (Memory st) x1 t lin stl2"
            using MTArray.IH[of x1 lin] by blast
          then show ?thesis
            using linDef sameAccess by auto
        qed
      next
        case (MTValue x)
        then show ?case by simp
      qed
    qed

    have subPOld_imp_new_cmp:"\<forall>stl2 x11 x12. CompMemType (Memory st) x t (MTArray x11 x12) p stl2 \<longrightarrow> CompMemType (Memory st') x t (MTArray x11 x12) p stl2"
    proof intros
      fix stl2 x11 x12
      assume in1:" CompMemType (Memory st) x t (MTArray x11 x12) p stl2"
      then show " CompMemType (Memory st') x t (MTArray x11 x12) p stl2" using asf pNotPrnt
      proof(induction t arbitrary:x p)
        case (MTArray x1 t)
        obtain iin lin where linDef: "iin<x \<and> accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) (Memory st) = Some (MPointer lin)
                                      \<and> (lin = stl2 \<and> MTArray x1 t = MTArray x11 x12 \<or> CompMemType (Memory st) x1 t (MTArray x11 x12) lin stl2)"
          using MTArray.prems(1) unfolding CompMemType.simps by blast
        have "(hash p (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) \<noteq> l" using MTArray.prems(3) ldef ShowLNatDot
          by (metis hash_injective)
        then have sameAccess:" accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) (Memory st') = accessStore (hash p
            (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) (Memory st)" using nonLocChanged by simp
        then show ?case
        proof(cases "lin = stl2")
          case True
          then show ?thesis using MTArray.prems sameAccess linDef
            by (metis (mono_tags, lifting) MTArray.IH CompMemType.simps(2) TypedMemSubPrefPtrs.simps(2))
        next
          case False
          then have "CompMemType (Memory st) x1 t (MTArray x11 x12) lin stl2" using linDef by simp
          moreover have "\<not> TypedMemSubPrefPtrs (Memory st) x1 t lin prnt" using MTArray.prems(2) linDef
            using sameAccess by auto
          moreover have " lin \<noteq> prnt" using MTArray.prems linDef
            using sameAccess by auto
          ultimately have "CompMemType (Memory st') x1 t (MTArray x11 x12) lin stl2"
            using MTArray.IH[of x1 lin] by blast
          then show ?thesis
            using linDef sameAccess by auto
        qed
      next
        case (MTValue x)
        then show ?case by simp
      qed
    qed

    have prntPNeg:"\<forall>stl2 x11 x12. \<not> TypedMemSubPrefPtrs (Memory st') x11 x12 stl2 p \<longrightarrow> \<not> TypedMemSubPrefPtrs (Memory st) x11 x12 stl2 p"
    proof intros
      fix stl2 x11 x12
      assume in1:"\<not> TypedMemSubPrefPtrs (Memory st') x11 x12 stl2 p"
      show "\<not> TypedMemSubPrefPtrs (Memory st) x11 x12 stl2 p "
      proof
        assume in2:"TypedMemSubPrefPtrs (Memory st) x11 x12 stl2 p"
        then show False using in1
        proof(induction x12 arbitrary:x11 stl2)
          case (MTArray x1 t)
          obtain iin lin where linDef: "iin<x11 \<and> accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) (Memory st) = Some (MPointer lin)
                                      \<and> (lin = p \<or> TypedMemSubPrefPtrs (Memory st) x1 t lin p)"
            using MTArray.prems(1) unfolding TypedMemSubPrefPtrs.simps by blast
          then show ?case
          proof(cases "(hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) = l")
            case True
            then have "accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) (Memory st') = Some (MPointer p)" using linDef 11 unfolding updateStore_def accessStore_def by simp
            then show ?thesis using MTArray.prems(2) linDef by auto
          next
            case False
            then have sameAccess:"accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) (Memory st) = accessStore (hash stl2
                (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) (Memory st')" using nonLocChanged by simp
            then show ?thesis
            proof(cases "lin = p")
              case True
              then show ?thesis using MTArray.prems(2) linDef sameAccess by auto
            next
              case False
              then have "TypedMemSubPrefPtrs (Memory st) x1 t lin p" using linDef by simp
              then show ?thesis using MTArray linDef sameAccess by auto
            qed
          qed
        next
          case (MTValue x)
          then show ?case by simp
        qed
      qed
    qed

    have subPNeg:"\<forall>stl2. \<not> TypedMemSubPrefPtrs (Memory st') x t p stl2 \<longrightarrow> \<not> TypedMemSubPrefPtrs (Memory st) x t p stl2"
    proof intros
      fix stl2
      assume in1:"\<not> TypedMemSubPrefPtrs (Memory st') x t p stl2"
      show "\<not> TypedMemSubPrefPtrs (Memory st) x t p stl2 "
      proof
        assume in2:" TypedMemSubPrefPtrs (Memory st) x t p stl2"
        then show False using in1 asf pNotPrnt
        proof(induction t arbitrary:x p)
          case (MTArray x1 t)
          obtain iin lin where linDef: "iin<x \<and> accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) (Memory st) = Some (MPointer lin)
                                      \<and> (lin = stl2 \<or> TypedMemSubPrefPtrs (Memory st) x1 t lin stl2)"
            using MTArray.prems(1) unfolding TypedMemSubPrefPtrs.simps by blast
          then have "(hash p (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) \<noteq> l" using ldef MTArray.prems ShowLNatDot
            by (metis hash_injective)

          then have sameAccess:"accessStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) (Memory st) = accessStore (hash p
              (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) (Memory st')" using nonLocChanged by simp
          then show ?thesis
          proof(cases "lin = stl2")
            case True
            then show ?thesis using MTArray.prems(2) linDef sameAccess by auto
          next
            case False
            then have "TypedMemSubPrefPtrs (Memory st) x1 t lin stl2" using linDef by simp
            then show ?thesis using MTArray linDef sameAccess
              by (metis TypedMemSubPrefPtrs.simps(2))
          qed
        next
          case (MTValue x)
          then show ?case by simp
        qed
      qed
    qed

    have prntPNeg_2:"\<forall>stl2 x11 x12 dloc1. \<not> TypedMemSubPrefPtrs (Memory st') x11 x12 stl2 p \<and> TypedMemSubPrefPtrs (Memory st') x11 x12 stl2 dloc1
                                  \<longrightarrow> TypedMemSubPrefPtrs (Memory st) x11 x12 stl2 dloc1 "
    proof intros
      fix stl2 x11 x12 dloc1
      assume in1:"\<not> TypedMemSubPrefPtrs (Memory st') x11 x12 stl2 p \<and> TypedMemSubPrefPtrs (Memory st') x11 x12 stl2 dloc1"
      then show "TypedMemSubPrefPtrs (Memory st) x11 x12 stl2 dloc1"
      proof(induction x12 arbitrary:x11 stl2)
        case (MTArray x1 t)
        obtain iin lin where linDef: "iin<x11 \<and> accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) (Memory st') = Some (MPointer lin)
                                    \<and> (lin = dloc1 \<or> TypedMemSubPrefPtrs (Memory st') x1 t lin dloc1)"
          using MTArray.prems(1) unfolding TypedMemSubPrefPtrs.simps by blast
        then show ?case
        proof(cases "(hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) = l")
          case True
          then have "accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) (Memory st') = Some (MPointer p)" using linDef 11 unfolding updateStore_def accessStore_def by simp
          then show ?thesis using MTArray.prems(1) linDef by auto
        next
          case False
          then have sameAccess:"accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) (Memory st) = accessStore (hash stl2
              (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) (Memory st')" using nonLocChanged by simp
          then show ?thesis
          proof(cases "lin = dloc1")
            case True
            then show ?thesis using MTArray.prems(1) linDef sameAccess by auto
          next
            case False
            then have "TypedMemSubPrefPtrs (Memory st') x1 t lin dloc1" using linDef by simp
            then show ?thesis using MTArray linDef sameAccess by auto
          qed
        qed
      next
        case (MTValue x)
        then show ?case by simp
      qed
    qed

    have prntPNeg_sublocs_comp:"\<forall>stl2 x11 x12 dloc1 dt. \<not> TypedMemSubPrefPtrs (Memory st') x11 x12 stl2 p \<and> CompMemType (Memory st) x11 x12 dt stl2 dloc1
                                  \<longrightarrow> CompMemType (Memory st') x11 x12 dt stl2 dloc1 "
    proof intros
      fix stl2 x11 x12 dloc1 dt
      assume in1:"\<not> TypedMemSubPrefPtrs (Memory st') x11 x12 stl2 p \<and> CompMemType (Memory st) x11 x12 dt stl2 dloc1"
      then show "CompMemType (Memory st') x11 x12 dt stl2 dloc1"
      proof(induction x12 arbitrary:x11 stl2)
        case (MTArray x1 t)
        obtain iin lin where linDef: "iin<x11 \<and> accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) (Memory st) = Some (MPointer lin)
                                    \<and> (lin = dloc1 \<and> MTArray x1 t = dt \<or> CompMemType (Memory st) x1 t dt lin dloc1)"
          using MTArray.prems(1) unfolding CompMemType.simps by blast
        then show ?case
        proof(cases "(hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) = l")
          case True
          then have "accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) (Memory st') = Some (MPointer p)" using linDef 11 unfolding updateStore_def accessStore_def by simp
          then show ?thesis using MTArray.prems(1) linDef by auto
        next
          case False
          then have sameAccess:"accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) (Memory st) = accessStore (hash stl2
              (ShowL\<^sub>n\<^sub>a\<^sub>t iin)) (Memory st')" using nonLocChanged by simp
          then show ?thesis
          proof(cases "lin = dloc1")
            case True
            then show ?thesis using MTArray.prems(1) linDef sameAccess
              using MTArray.IH by auto
          next
            case False
            then have "CompMemType (Memory st) x1 t dt lin dloc1" using linDef by simp
            then show ?thesis using MTArray linDef sameAccess by auto
          qed
        qed
      next
        case (MTValue x)
        then show ?case by simp
      qed
    qed

    have pPrntsLim:"\<forall>x11 x12 stl2. CompMemType (Memory st) x11 x12 (MTArray x t) stl2 p \<and> accessStore l (Memory st) \<noteq>
        Some (MPointer p) \<and> TypedMemSubPrefPtrs (Memory st) x11 x12 stl2 p \<and>
  MCon (MTArray x11 x12) (Memory st) stl2 \<longrightarrow> CompMemType (Memory st') x11 x12 (MTArray x t) stl2 p"
    proof(intros)
      fix x11 x12 stl2
      assume "CompMemType (Memory st) x11 x12 (MTArray x t) stl2 p \<and>
     accessStore l (Memory st) \<noteq> Some (MPointer p) \<and> TypedMemSubPrefPtrs (Memory st) x11 x12 stl2 p \<and> MCon (MTArray x11 x12) (Memory st) stl2"
      then show "CompMemType (Memory st') x11 x12 (MTArray x t) stl2 p"
      proof(induction x12 arbitrary: x11 stl2)
        case (MTArray x1 x12)
        obtain inI inL where inDef:"inI<x11 \<and> accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t inI)) (Memory st) = Some (MPointer inL)
                            \<and> (inL = p \<or> TypedMemSubPrefPtrs (Memory st) x1 x12 inL p)"
          using MTArray.prems unfolding TypedMemSubPrefPtrs.simps by blast
        then show ?case
        proof(cases "inL = p")
          case True
          then show ?thesis
            by (metis MTArray.prems inDef
                existingLocation_imps_allLocs_same nonLocChanged CompMemType.simps(2))
        next
          case False
          then have "TypedMemSubPrefPtrs (Memory st) x1 x12 inL p" using inDef by auto
          moreover have "accessStore l (Memory st) \<noteq> Some (MPointer p)" using MTArray.prems by simp
          moreover have "MCon (MTArray x1 x12) (Memory st) inL" using MTArray.prems inDef
            using MconSameTypeSameAccessWithTyping by blast
          moreover have "CompMemType (Memory st) x1 x12 (MTArray x t) inL p"
            by (meson False MTArray.prems existingLocation_imps_allLocs inDef)
          ultimately have "CompMemType (Memory st') x1 x12 (MTArray x t) inL p" using MTArray.IH[of x1 inL] by blast
          moreover have "accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t inI)) (Memory st) = accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t inI)) (Memory st')"
          proof -
            obtain nn :: "nat \<Rightarrow> String.literal \<Rightarrow> String.literal \<Rightarrow> nat" where
              f1: "\<forall>X1 X4 X5. (\<exists>X7. hash X4 (ShowL\<^sub>n\<^sub>a\<^sub>t X7) = X5 \<and> X7 < X1) \<longrightarrow> hash
                  X4 (ShowL\<^sub>n\<^sub>a\<^sub>t (nn X1 X4 X5)) = X5 \<and> nn X1 X4 X5 < X1"
              by moura
            obtain nna :: "String.literal \<Rightarrow> String.literal \<Rightarrow> nat \<Rightarrow> mtypes \<Rightarrow> nat" and nnb
                :: "String.literal \<Rightarrow> String.literal \<Rightarrow> nat \<Rightarrow> mtypes \<Rightarrow> nat" where
              f2: "\<forall>l la n m. (TypedMemSubPref l la (MTArray n m) \<or> (\<forall>na. hash la (ShowL\<^sub>n\<^sub>a\<^sub>t na) \<noteq> l
          \<and> \<not> TypedMemSubPref l (hash la (ShowL\<^sub>n\<^sub>a\<^sub>t na)) m \<or> \<not> na < n)) \<and> ((hash la (ShowL\<^sub>n\<^sub>a\<^sub>t(nna l la n m)) = l
            \<or> TypedMemSubPref l (hash la (ShowL\<^sub>n\<^sub>a\<^sub>t(nna l la n m))) m) \<and> nna l la n m < n \<or> \<not> TypedMemSubPref l la (MTArray n m))"
              using TypedMemSubPref.simps(2) by moura
            obtain nnc :: "nat \<Rightarrow> String.literal \<Rightarrow> String.literal \<Rightarrow> nat" where
              f3: "\<forall>s n t m l la. (CompMemType s n (MTValue t) m l la \<or> (\<forall>na. hash l (ShowL\<^sub>n\<^sub>a\<^sub>t na) \<noteq> la \<or> \<not> na < n)
        \<or> MTValue t \<noteq> m) \<and> ((hash l (ShowL\<^sub>n\<^sub>a\<^sub>t(nnc n l la)) = la \<and> nnc n l la < n) \<and> MTValue t = m \<or> \<not> CompMemType s n (MTValue t) m l la)"
              using f1 CompMemType.simps(1) by moura
            obtain ll :: "String.literal \<Rightarrow> nat \<Rightarrow> mtypes \<Rightarrow> (mtypes, memoryvalue) typedstore \<Rightarrow> String.literal"
                  and lla :: "String.literal \<Rightarrow> nat \<Rightarrow> mtypes \<Rightarrow> memoryvalue store \<Rightarrow> String.literal" where
                f4: "TypedMemSubPref (ll inL x1 x12 (Memory st)) inL (MTArray x1 x12) \<or> TypedMemSubPref p inL (MTArray x1 x12)"
              by (meson CompMemType_imps_TypedMemSubPrefPtrs \<open>CompMemType (Memory st) x1 x12 (MTArray x t) inL p\<close> selfPoint_imps_TypedMemSubPref)
            obtain tt :: "mtypes \<Rightarrow> types" and nnd :: "mtypes \<Rightarrow> nat" and mm :: "mtypes \<Rightarrow> mtypes" where
              "x12 = MTArray (nnd x12) (mm x12) \<or> x12 = MTValue (tt x12) \<or> 0 = x1"
              by (metis (no_types) \<open>MCon (MTArray x1 x12) (Memory st) inL\<close> bot_nat_0.not_eq_extremum mcon_accessStore)
            then show ?thesis
              using f4 f3 f2 by (metis CompMemType_imps_CompMemJustType MConSubTypes memoryvalue.inject(2) \<open>CompMemType (Memory st)
                  x1 x12 (MTArray x t) inL p\<close> \<open>MCon (MTArray x1 x12) (Memory st) inL\<close> inDef lOrigin less_nat_zero_code
                  mconlOld nonLocChanged option.inject CompMemJustType.simps(2) CompMemType.simps(2))
          qed
          ultimately show ?thesis using inDef unfolding CompMemType.simps by metis
        qed
      next
        case (MTValue x)
        then show ?case by simp
      qed

    qed

    have getToPrntNew_imps_Old:"\<forall>stl2 x11 x12. TypedMemSubPrefPtrs (Memory st') x11 x12 stl2 prnt \<and> prnt \<noteq> stl2
        \<longrightarrow> TypedMemSubPrefPtrs (Memory st) x11 x12 stl2 prnt"
    proof intros
      fix stl2 x11 x12
      assume "TypedMemSubPrefPtrs (Memory st') x11 x12 stl2 prnt \<and> prnt \<noteq> stl2"
      then show "TypedMemSubPrefPtrs (Memory st) x11 x12 stl2 prnt"
      proof(induction x12 arbitrary:x11 stl2)
        case (MTArray x1 x12)
        obtain ii ll where llDef:"ii<x11 \<and> accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) (Memory st') = Some (MPointer ll)
                                \<and> (ll = prnt \<or> TypedMemSubPrefPtrs (Memory st') x1 x12 ll prnt)"
          using MTArray.prems(1) unfolding TypedMemSubPrefPtrs.simps by blast

        then show ?case
        proof(cases "(hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) = l")
          case True
          then have "stl2 = prnt" using ldef ShowLNatDot
            using hash_injective by blast
          then show ?thesis using MTArray.prems(1) by auto
        next
          case False
          then have same:" accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) (Memory st') = accessStore (hash stl2
              (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) (Memory st)" using nonLocChanged by simp
          then show ?thesis
          proof(cases "ll = prnt")
            case True
            then show ?thesis using same llDef by force
          next
            case False
            then have "TypedMemSubPrefPtrs (Memory st') x1 x12 ll prnt" using llDef by simp
            then show ?thesis using MTArray.IH[of x1 ll] same False llDef by force
          qed
        qed
      next
        case (MTValue x)
        then show ?case by simp
      qed
    qed

    have prntPrntNeg:"\<forall>stl2 x11 x12. \<not> TypedMemSubPrefPtrs (Memory st') x11 x12 stl2 prnt \<and> prnt \<noteq> stl2
        \<longrightarrow> \<not> TypedMemSubPrefPtrs (Memory st) x11 x12 stl2 prnt"
    proof intros
      fix stl2 x11 x12
      assume in1:"\<not> TypedMemSubPrefPtrs (Memory st') x11 x12 stl2 prnt \<and> prnt \<noteq> stl2"
      show "\<not> TypedMemSubPrefPtrs (Memory st) x11 x12 stl2 prnt "
      proof
        assume in2:"TypedMemSubPrefPtrs (Memory st) x11 x12 stl2 prnt"
        then show False using in1
        proof(induction x12 arbitrary:x11 stl2)
          case (MTArray x1 t)
          obtain iIn lin where linDef: "iIn<x11 \<and> accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t iIn)) (Memory st) = Some (MPointer lin)
                                      \<and> (lin = prnt \<or> TypedMemSubPrefPtrs (Memory st) x1 t lin prnt)"
            using MTArray.prems(1) unfolding TypedMemSubPrefPtrs.simps by blast
          then show ?case
          proof(cases "(hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t iIn)) = l")
            case True
            then have "stl2 = prnt" using ldef ShowLNatDot
              using hash_injective by blast
            then show ?thesis using MTArray.prems(2) linDef by simp
          next
            case False
            then have sameAccess:"accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t iIn)) (Memory st) = accessStore (hash stl2
                (ShowL\<^sub>n\<^sub>a\<^sub>t iIn)) (Memory st')" using nonLocChanged by simp
            then show ?thesis
            proof(cases "lin = prnt")
              case True
              then show ?thesis using MTArray.prems(2) linDef sameAccess by auto
            next
              case False
              then have "TypedMemSubPrefPtrs (Memory st) x1 t lin prnt" using linDef by simp
              then show ?thesis using MTArray linDef sameAccess by auto
            qed
          qed
        next
          case (MTValue x)
          then show ?case by simp
        qed
      qed
    qed


    have prntLim3Neg:"\<forall>x11' x12' stl2 stl1. \<not>TypedMemSubPrefPtrs (Memory st') x11' x12' stl2 stl1 \<and> \<not> TypedMemSubPrefPtrs (Memory st) len' arr' prnt stl1 \<and>
          stl2 \<noteq> prnt \<and> ( \<forall>new newt. CompMemType (Memory st) x11' x12' newt stl2 new \<and> new = prnt \<longrightarrow> newt = MTArray len' arr')
          \<longrightarrow> \<not>TypedMemSubPrefPtrs (Memory st) x11' x12' stl2 stl1"
    proof intros
      fix x11' x12' stl2 stl1
      assume "\<not>TypedMemSubPrefPtrs (Memory st') x11' x12' stl2 stl1 \<and>
     \<not> TypedMemSubPrefPtrs (Memory st) len' arr' prnt stl1 \<and>
     stl2 \<noteq> prnt \<and> (\<forall>new newt. CompMemType (Memory st) x11' x12' newt stl2 new \<and> new = prnt \<longrightarrow> newt = MTArray len' arr')"
      then have in1:"\<not>TypedMemSubPrefPtrs (Memory st') x11' x12' stl2 stl1"
          and "\<not> TypedMemSubPrefPtrs (Memory st) len' arr' prnt stl1"
          and "stl2 \<noteq> prnt"
          and " (\<forall>new newt. CompMemType (Memory st) x11' x12' newt stl2 new \<and> new = prnt \<longrightarrow> newt = MTArray len' arr')" by simp+
      then show "\<not>TypedMemSubPrefPtrs (Memory st) x11' x12' stl2 stl1"
      proof(induction x12' arbitrary:x11' stl2)
        case (MTArray x1 x12')
        then have iiNeg: "\<forall>i<x11'. \<exists>l. accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') \<noteq> Some (MPointer l)
                                        \<or> (l \<noteq> stl1 \<and> \<not>TypedMemSubPrefPtrs (Memory st') x1 x12' l stl1)"
          unfolding TypedMemSubPrefPtrs.simps by blast
        show ?case
        proof
          assume "TypedMemSubPrefPtrs (Memory st) x11' (MTArray x1 x12') stl2 stl1"
          then obtain ii ll where iiDef: "ii<x11' \<and> accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) (Memory st) = Some (MPointer ll)
                    \<and> (ll = stl1 \<or> TypedMemSubPrefPtrs (Memory st) x1 x12' ll stl1)"
            unfolding TypedMemSubPrefPtrs.simps by blast
          then have "(hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) \<noteq> l" using ldef hash_injective ShowLNatDot MTArray.prems by blast
          then have same:" accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) (Memory st') = accessStore (hash stl2
              (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) (Memory st)" using nonLocChanged by simp
          show False
          proof(cases "ll = stl1")
            case True
            then show ?thesis using iiDef same iiNeg
              using MTArray.prems(1) by auto
          next
            case False
            then have s:"TypedMemSubPrefPtrs (Memory st) x1 x12' ll stl1" using iiDef by simp
            have llNotPrnt:"ll \<noteq> prnt"
            proof
              assume *:"ll = prnt"
              then have "MTArray x1 x12' = MTArray len' arr'" using MTArray.prems(4) iiDef by auto
              then show False using s MTArray.prems(2) * by simp
            qed
            then show ?thesis using same MTArray.IH[OF ] iiDef MTArray.prems(4)
              by (metis MTArray.prems(1,2) CompMemType.simps(2) TypedMemSubPrefPtrs.simps(2))
          qed
        qed

      next
        case (MTValue x)
        then show ?case by simp
      qed
    qed

    have prntLim4:"\<forall>x11' x12' stl2 stl1 dt. CompMemType (Memory st) x11' x12' dt stl2 stl1 \<and> \<not> TypedMemSubPrefPtrs (Memory st) len' arr' prnt stl1 \<and>
          stl2 \<noteq> prnt \<and> ( \<forall>new newt. CompMemType (Memory st) x11' x12' newt stl2 new \<and> new = prnt
              \<longrightarrow> newt = MTArray len' arr') \<and> MCon (MTArray x11' x12') (Memory st) stl2
          \<longrightarrow> CompMemType (Memory st') x11' x12' dt stl2 stl1"
    proof intros
      fix x11' x12' stl2 stl1 dt
      assume "CompMemType (Memory st) x11' x12' dt stl2 stl1 \<and>
     \<not> TypedMemSubPrefPtrs (Memory st) len' arr' prnt stl1 \<and>
     stl2 \<noteq> prnt \<and> (\<forall>new newt. CompMemType (Memory st) x11' x12' newt stl2 new \<and> new = prnt \<longrightarrow>
         newt = MTArray len' arr') \<and> MCon (MTArray x11' x12') (Memory st) stl2"
      then have in1:"CompMemType (Memory st) x11' x12' dt stl2 stl1"
          and "\<not> TypedMemSubPrefPtrs (Memory st) len' arr' prnt stl1"
          and "stl2 \<noteq> prnt"
          and " (\<forall>new newt. CompMemType (Memory st) x11' x12' newt stl2 new \<and> new = prnt \<longrightarrow> newt = MTArray len' arr')"
          and "MCon (MTArray x11' x12') (Memory st) stl2" by blast+
      then show "CompMemType (Memory st') x11' x12' dt stl2 stl1"
      proof(induction x12' arbitrary:x11' stl2)
        case (MTArray x1 x12')
        then obtain ii ll where iiDef: "ii<x11' \<and> accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) (Memory st) = Some (MPointer ll)
                    \<and> (ll = stl1 \<and> MTArray x1 x12' = dt \<or> CompMemType (Memory st) x1 x12' dt ll stl1)"
          unfolding CompMemType.simps by blast
        then have "(hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) \<noteq> l" using ldef hash_injective ShowLNatDot MTArray.prems by blast
        then have same:" accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) (Memory st') = accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) (Memory st)" using nonLocChanged by simp
        then show ?case
        proof(cases "ll = stl1")
          case True
          then have "MTArray x1 x12' = dt" using iiDef True
            by (metis MTArray.prems(1,5) existingLocation_imps_allLocs_same)
          then show ?thesis using iiDef same True by force
        next
          case False
          then have s:"CompMemType (Memory st) x1 x12' dt ll stl1" using iiDef by simp
          have llNotPrnt:"ll \<noteq> prnt"
          proof
            assume *:"ll = prnt"
            then have "MTArray x1 x12' = MTArray len' arr'" using MTArray.prems(4) iiDef same by auto
            then show False using s MTArray.prems(2) * same
              by (simp add: CompMemType_imps_TypedMemSubPrefPtrs)
          qed
          have "MCon (MTArray x1 x12') (Memory st) ll" using MTArray.prems(5) iiDef
            using MconSameTypeSameAccessWithTyping by blast
          then have "CompMemType (Memory st') x1 x12' dt ll stl1"
            using MTArray.IH[OF s MTArray.prems(2) llNotPrnt] iiDef MTArray.prems(4,5) by auto
          then show ?thesis using same iiDef by auto
        qed
      next
        case (MTValue x)
        then show ?case by simp
      qed
    qed

    have prntLim5:"\<forall>x11' x12' stl2 dloc1 dt. TypedMemSubPrefPtrs (Memory st') x11' x12' stl2 dloc1
                      \<and> (\<forall>new newt. CompMemType (Memory st) x11' x12' newt stl2 new \<and> new = dloc1 \<longrightarrow> newt = dt)
                    \<and> stl2 \<noteq> prnt \<and> \<not> TypedMemSubPrefPtrs (Memory st') len' arr' prnt dloc1
                  \<and> (\<forall>new newt. CompMemType (Memory st') x11' x12' newt stl2 new \<and> new = prnt \<longrightarrow> newt = MTArray len' arr')
                    \<longrightarrow> CompMemType (Memory st') x11' x12' dt stl2 dloc1"
    proof intros
      fix x11' x12' stl2 dloc1 dt
      assume " TypedMemSubPrefPtrs (Memory st') x11' x12' stl2 dloc1 \<and>
     (\<forall>new newt. CompMemType (Memory st) x11' x12' newt stl2 new \<and> new = dloc1 \<longrightarrow> newt = dt) \<and>
     stl2 \<noteq> prnt \<and>
     \<not> TypedMemSubPrefPtrs (Memory st') len' arr' prnt dloc1 \<and> (\<forall>new newt. CompMemType (Memory st') x11' x12' newt stl2
         new \<and> new = prnt \<longrightarrow> newt = MTArray len' arr')"
      then have " TypedMemSubPrefPtrs (Memory st') x11' x12' stl2 dloc1" and
        "(\<forall>new newt. CompMemType (Memory st) x11' x12' newt stl2 new \<and> new = dloc1 \<longrightarrow> newt = dt)"
          and "stl2 \<noteq> prnt"
          and "\<not> TypedMemSubPrefPtrs (Memory st') len' arr' prnt dloc1"
          and "(\<forall>new newt. CompMemType (Memory st') x11' x12' newt stl2 new \<and> new = prnt \<longrightarrow> newt = MTArray len' arr')" by blast+
      then show "CompMemType (Memory st') x11' x12' dt stl2 dloc1"
      proof(induction x12' arbitrary: x11' stl2)
        case (MTArray x1 x12')
        obtain ii ll where iiDef:"ii<x11' \<and> accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) (Memory st') = Some (MPointer ll)
                                    \<and> (ll = dloc1 \<or> TypedMemSubPrefPtrs (Memory st') x1 x12' ll dloc1)"
          using MTArray.prems(1) unfolding TypedMemSubPrefPtrs.simps by auto
        then have "(hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) \<noteq> l" using ldef hash_injective ShowLNatDot MTArray.prems(3) by blast
        then have same:"accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) (Memory st') = accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) (Memory st)" using nonLocChanged by simp
        then show ?case
        proof(cases "ll = dloc1")
          case True
          then have "(MTArray x1 x12') = dt" using iiDef MTArray.prems(2) same by auto
          then show ?thesis using iiDef True by force
        next
          case False
          then have cc1:"TypedMemSubPrefPtrs (Memory st') x1 x12' ll dloc1" using iiDef by simp
          have cc2:"\<forall>new newt. CompMemType (Memory st) x1 x12' newt ll new \<and> new = dloc1 \<longrightarrow> newt = dt" using iiDef MTArray.prems(2) same by auto
          have cc3:"ll \<noteq> prnt"
          proof
            assume *:"ll = prnt"
            then have "(MTArray x1 x12') = MTArray len' arr'" using MTArray.prems(5) iiDef by auto
            then show False using MTArray.prems(4) cc1 * by simp
          qed
          have "\<forall>new newt. CompMemType (Memory st') x1 x12' newt ll new \<and> new = prnt \<longrightarrow> newt = MTArray len' arr'" using MTArray.prems(5) same iiDef by force
          then have "CompMemType (Memory st') x1 x12' dt ll dloc1"
            using MTArray.IH[OF cc1 cc2 cc3 MTArray.prems(4)] MTArray.prems iiDef same by blast
          then show ?thesis using iiDef same by auto
        qed
      next
        case (MTValue x)
        show ?case using MTValue(1,2) by auto
      qed
    qed

    have prntLim6:"\<forall>x11' x12' stl2 dloc1. \<not> TypedMemSubPrefPtrs (Memory st') x11' x12' stl2 prnt\<and> TypedMemSubPrefPtrs (Memory st') x11' x12' stl2 dloc1\<and> stl2 \<noteq> prnt
            \<longrightarrow> TypedMemSubPrefPtrs (Memory st) x11' x12' stl2 dloc1"
    proof intros
      fix x11' x12' stl2 dloc1
      assume " \<not> TypedMemSubPrefPtrs (Memory st') x11' x12' stl2 prnt \<and> TypedMemSubPrefPtrs (Memory st') x11' x12' stl2 dloc1 \<and> stl2 \<noteq> prnt"
      then show "TypedMemSubPrefPtrs (Memory st) x11' x12' stl2 dloc1 "
      proof(induction x12' arbitrary:x11' stl2)
        case (MTArray x1 x12')
        obtain ii ll where iiDef:"ii<x11' \<and> accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) (Memory st') = Some (MPointer ll) \<and>
                                       (ll = dloc1 \<or> TypedMemSubPrefPtrs (Memory st') x1 x12' ll dloc1)"
          using MTArray.prems unfolding TypedMemSubPrefPtrs.simps by blast
        then have "(hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) \<noteq> l" using ldef hash_injective ShowLNatDot MTArray by blast
        then have same:"accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) (Memory st') =accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) (Memory st)" using nonLocChanged by simp
        then show ?case
        proof(cases "ll = dloc1")
          case True
          then show ?thesis using same iiDef by force
        next
          case False
          then show ?thesis using iiDef same MTArray by auto
        qed
      next
        case (MTValue x)
        then show ?case by auto
      qed
    qed

    have prntLim7:"\<forall>x11' x12' stl2 stl1 dt.(\<forall>new newt. CompMemType (Memory st) x11' x12' newt stl2 new \<and> new = stl1 \<longrightarrow> newt = dt)
                   \<and> \<not> TypedMemSubPrefPtrs (Memory st') x11' x12' stl2 prnt \<and> stl2 \<noteq> prnt
                   \<and> TypedMemSubPrefPtrs (Memory st') x11' x12' stl2 stl1
                    \<longrightarrow> CompMemType (Memory st') x11' x12' dt stl2 stl1"
    proof intros
      fix x11' x12' stl2 stl1 dt
      assume "(\<forall>new newt. CompMemType (Memory st) x11' x12' newt stl2 new \<and> new = stl1 \<longrightarrow> newt = dt) \<and>
     \<not> TypedMemSubPrefPtrs (Memory st') x11' x12' stl2 prnt \<and> stl2 \<noteq> prnt \<and> TypedMemSubPrefPtrs (Memory st') x11' x12' stl2 stl1"
      then have "(\<forall>new newt. CompMemType (Memory st) x11' x12' newt stl2 new \<and> new = stl1 \<longrightarrow> newt = dt)"
          and "\<not> TypedMemSubPrefPtrs (Memory st') x11' x12' stl2 prnt"
          and "stl2 \<noteq> prnt"
          and "TypedMemSubPrefPtrs (Memory st') x11' x12' stl2 stl1" by blast+
      then show "CompMemType (Memory st') x11' x12' (dt) stl2 stl1"
      proof(induction x12' arbitrary:x11' stl2)
        case (MTArray x1 x12')
        then obtain ii ll where iiDef:"ii<x11' \<and> accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) (Memory st') = Some (MPointer ll)
                                      \<and> (ll = stl1 \<or> TypedMemSubPrefPtrs (Memory st') x1 x12' ll stl1)"
          unfolding TypedMemSubPrefPtrs.simps by blast
        then have "(hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) \<noteq> l" using MTArray.prems ldef ShowLNatDot hash_injective by blast
        then have same:"accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) (Memory st') =accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) (Memory st)" using nonLocChanged by simp
        then show ?case
        proof(cases "ll = stl1")
          case True
          then show ?thesis using same MTArray.prems(1) iiDef by force
        next
          case False
          then show ?thesis using same MTArray iiDef
            by (metis (no_types, opaque_lifting) CompMemType.simps(2) TypedMemSubPrefPtrs.simps(2))
        qed
      next
        case (MTValue x)
        then show ?case by auto
      qed
    qed

    have prntLim8:"\<forall>x11' x12' stl2 stl1. \<not> TypedMemSubPrefPtrs (Memory st') x11' x12' stl2 stl1 \<and>
                  \<not> TypedMemSubPrefPtrs (Memory st') x11' x12' stl2 prnt \<and> stl2 \<noteq> prnt
                  \<longrightarrow> \<not> TypedMemSubPrefPtrs (Memory st) x11' x12' stl2 stl1"
    proof intros
      fix x11' x12' stl2 stl1
      assume "\<not> TypedMemSubPrefPtrs (Memory st') x11' x12' stl2 stl1 \<and> \<not> TypedMemSubPrefPtrs (Memory st') x11' x12' stl2 prnt \<and> stl2 \<noteq> prnt"
      then show "\<not> TypedMemSubPrefPtrs (Memory st) x11' x12' stl2 stl1"
      proof(induction x12' arbitrary:x11' stl2)
        case (MTArray x1 x12')

        show ?case
        proof
          assume *:"TypedMemSubPrefPtrs (Memory st) x11' (MTArray x1 x12') stl2 stl1"
          then obtain ii ll where iiDef:"ii<x11' \<and> accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) (Memory st) = Some (MPointer ll)
                                          \<and> (ll = stl1 \<or> TypedMemSubPrefPtrs (Memory st) x1 x12' ll stl1)"
            unfolding TypedMemSubPrefPtrs.simps by blast
          then have " (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) \<noteq> l" using ldef hash_injective ShowLNatDot MTArray.prems by blast
          then have same:"accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) (Memory st) = accessStore (hash stl2
              (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) (Memory st')" using nonLocChanged by simp
          show False
          proof(cases "ll = stl2")
            case True
            then show ?thesis using iiDef same MTArray.prems
              using MTArray.IH by force
          next
            case False
            then show ?thesis using iiDef same MTArray by auto
          qed
        qed
      next
        case (MTValue x)
        then show ?case by simp
      qed
    qed


    show ?thesis unfolding TypeSafe_def StateInvariant_def
    proof intros
      show "AddressTypes (Accounts st')" using 2(1) 11 unfolding TypeSafe_def by simp
    next
      show "unique_locations (Denvalue env)" using 2(1) unfolding TypeSafe_def by simp
    next
      have a0:" compPointers (Stack st) (Denvalue env)" using 2(1) unfolding TypeSafe_def by blast
      then show "compPointers (Stack st') (Denvalue env)" using sameStack sameStorage by simp
    next
      show "safeContract (Accounts st') (Storage st')" using sameStorage 11 2(1) unfolding TypeSafe_def safeContract_def by auto
    next
      show "balanceTypes (Accounts st')" using 11 using 2(1) unfolding TypeSafe_def by simp
    next
      have "envAddressesWellFormed env" using 2(1) unfolding TypeSafe_def by simp
      then show "addressFormat (Address env)" and "addressFormat (Sender env)" by simp+
    next
      show "svalueTypes (Svalue env)" using 2(1) unfolding TypeSafe_def by simp
    next
      have *:"((\<forall>tloc loc. Toploc (Stack st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Stack st) = None) \<and>
            (\<forall>loc y. accessStore loc (Stack st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Stack st). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))) "
        using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by simp
      have **:"Toploc (Stack st) = Toploc (Stack st')" using 11 unfolding updateStore_def by auto
      show "lessThanTopLocs (Stack st')" unfolding lessThanTopLocs_def
      proof intros

        fix tloc loc
        assume h1:"Toploc (Stack st') \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
        then have "Toploc (Stack st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)" using ** by simp
        then show "accessStore loc (Stack st') = None" using *
          by (simp add: sameStack)
      next
        fix loc y
        assume h1:" accessStore loc (Stack st') = Some y"
        then show "\<exists>tloc<Toploc (Stack st'). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)" using ** *
          by (metis sameStack)
      qed
    next
      show "lessThanTopLocs cd" using 2(1) unfolding TypeSafe_def by simp
    next
      have a12:"Toploc (Memory st) = Toploc (Memory st')" using 11 unfolding updateStore_def by auto
      have a15:"lessThanTopLocs (Memory st)" using 2 unfolding TypeSafe_def by simp
      have tloc:"Toploc (Memory st) < Toploc (snd (allocate (Memory st)))" unfolding allocate_def by simp
      show "lessThanTopLocs (Memory st')" unfolding lessThanTopLocs_def
      proof intros
        fix tloc loc
        assume b10: "Toploc (Memory st') \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
        then have b20:"Toploc (Memory st) \<le> tloc" using a12 tloc a12
          by force

        then show "accessStore loc (Memory st') = None "
          by (metis a15 b10 lOrigin lessThanSome_imps_Locs lessThanTopLocs_def linorder_not_less nonLocChanged)
      next
        fix loc y
        assume "accessStore loc (Memory st') = Some y "
        then show "\<exists>tloc<Toploc (Memory st'). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
          by (metis a12 a15 lOrigin lessThanTopLocs_def nonLocChanged)
      qed
    next
      show "typeCompat (Denvalue env) (Stack st') (Memory st') (Storage st' (Address env)) cd"
        unfolding typeCompat_def
      proof intros
        fix tLook lLook
        assume inDen:" (tLook, lLook) |\<in>| fmran (Denvalue env)"
        show " denvalueCon (Stack st') (Memory st') (Storage st' (Address env)) cd tLook lLook"
        proof(cases lLook)
          case (Stackloc x1)
          then show ?thesis
          proof(cases "accessStore x1 (Stack st')")
            case None
            then show ?thesis using 2(1) unfolding TypeSafe_def typeCompat_def using sameStorage inDen sameStack Stackloc by force
          next
            case (Some a)
            then show ?thesis
            proof(cases a)
              case (KValue x1')
              then show ?thesis using 2(1) unfolding TypeSafe_def typeCompat_def using sameStorage inDen sameStack Stackloc Some by force
            next
              case (KCDptr x2)
              then show ?thesis using 2(1) unfolding TypeSafe_def typeCompat_def using sameStorage inDen sameStack Stackloc Some by force
            next
              case (KMemptr x3)
              then obtain struct where stT: "tLook = type.Memory struct" using 2(1) unfolding TypeSafe_def typeCompat_def using sameStorage inDen sameStack Stackloc Some
                by (cases tLook; fastforce)
              have mcOld:"MCon struct (Memory st) x3"
                using sameStorage inDen sameStack Stackloc Some KMemptr by (metis 2(1) sameMemTSafe stT)
              have tps:"(case struct of MTArray len arr \<Rightarrow> \<forall>i<len. accessTypeStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr
                           | MTValue val \<Rightarrow> accessTypeStore x3 (Memory st) = Some (MTValue val))"
                using 2(1) unfolding TypeSafe_def denvalueTypeCorrectness_def
                using inDen sameStack Stackloc Some KMemptr stT by simp
              have nc:"\<forall>locs. locs \<noteq> l \<longrightarrow> accessStore locs (Memory st) = accessStore locs (Memory st')" using nonLocChanged by simp
              have subt:"subPrefixStructuralConsistency (Memory st)" using 2(1) unfolding TypeSafe_def by simp
              have "accessTypeStore l (Memory st) = Some (MTArray x t)" using lInfo 11 by auto
              then have "MCon struct (Memory st') x3"
                using 11(4) cpm2m_singleLChange[OF mcOld tps _ _ _ mcPNew subt nc ] lOrigin
                by simp
              then show ?thesis using sameStorage inDen sameStack Stackloc Some KMemptr stT by simp
            next
              case (KStoptr x4)
              then show ?thesis using 2(1) unfolding TypeSafe_def typeCompat_def using sameStorage inDen sameStack Stackloc Some by (cases tLook; force)
            qed
          qed
        next
          case (Storeloc x2)
          then show ?thesis using 2(1) unfolding TypeSafe_def typeCompat_def using sameStorage inDen
            by (metis denvalue.simps(6))
        qed
      qed
      then have "typeCompat (Denvalue env) (Stack st) (Memory st') (Storage st' (Address env)) cd " using sameStack by simp
    next
      have "Accounts st'= Accounts st" using 11 by auto
      then show "fullyInitialised env (Accounts st') (Stack st')" using 2(3) 11 unfolding fullyInitialised_def by auto
    next
      have sameACCT:"\<forall>locs. accessTypeStore locs (Memory st) = accessTypeStore locs (Memory st')"
        using 11 lInfo unfolding accessTypeStore_def updateStore_def by auto

      show "denvalueTypeCorrectness env (Stack st') (Memory st') "
        unfolding denvalueTypeCorrectness_def
      proof(intros)
        fix t2 l2 ptr_loc sub_loc
        assume *:"(type.Memory t2, Stackloc l2) |\<in>| fmran (Denvalue env) \<and> accessStore l2 (Stack st') = Some (KMemptr ptr_loc)"

        show "case t2 of
       MTArray len arr \<Rightarrow>
       (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr)
     | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st') = Some (MTValue val)"
        proof -
          have sameACC:"accessStore l2 (Stack st') = accessStore l2 (Stack st)"
            using * 11 unfolding accessStore_def updateStore_def by simp
          then have mcOld:"MCon t2 (Memory st) ptr_loc" using * by (metis 2(1) sameMemTSafe)
          then have old:"(case t2 of
                         MTArray len arr \<Rightarrow>
         (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr)

       | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st) = Some (MTValue val))"
            using sameACC 2(1) * TypeSafe_def denvalueTypeCorrectness_def by auto

          have inDenvalue:"(type.Memory t2, Stackloc l2) |\<in>| fmran (Denvalue env)" using * by simp

          then show ?thesis
          proof(cases t2)
            case (MTArray x11 x12)
            then have mcOld:"MCon (MTArray x11 x12) (Memory st) ptr_loc" using mcOld by blast

            then have conc1:"(\<forall>i<x11. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some x12)"
              using sameACCT old MTArray by simp
            then show ?thesis using MTArray
              using lOrigin nonLocChanged old sameACCT by auto
          next
            case (MTValue x2)
            have "accessTypeStore ptr_loc (Memory st') = Some (MTValue x2)"
              using MTValue old sameACCT by auto
            then show ?thesis using MTValue by auto
          qed
        qed
      qed
    next
      have oldSub:"subPrefixStructuralConsistency (Memory st)"
        using 2(1) unfolding TypeSafe_def by simp
      show "subPrefixStructuralConsistency (Memory st')"
        unfolding subPrefixStructuralConsistency_def
      proof intros
        fix locs tp
        assume in1:" accessTypeStore locs (Memory st') = Some tp "
        have sameTy:"\<forall>locs. accessTypeStore locs (Memory st) = accessTypeStore locs (Memory st') "
          using 11 unfolding updateStore_def accessTypeStore_def by auto
        show "case accessStore locs (Memory st') of None \<Rightarrow> False
              | Some (MValue v) \<Rightarrow> \<exists>val. MCon tp (Memory st') locs \<and> tp = MTValue val \<and> accessTypeStore locs (Memory st') = Some tp
              | Some (MPointer p) \<Rightarrow>
                 \<exists>len arr.
                    MCon tp (Memory st') p \<and>
                    tp = MTArray len arr \<and>
                    (\<forall>i<len. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr)"
        proof(cases "locs = l")
          case True
          have actO:"accessTypeStore l (Memory st) = Some (MTArray x t)"
            using lInfo 11 nonLocChanged by auto
          then have tpDef:"tp = MTArray x t"
            using sameTy True in1 by simp
          then have ptr:"accessStore locs (Memory st') = Some (MPointer p)"
            using 11(4) True by simp
          moreover have " MCon tp (Memory st') p"
            using tpDef mcPNew by fastforce
          moreover have "(\<forall>i<x. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some t)"
            using sameTy pTAccessOld by simp
          ultimately show ?thesis using True tpDef ptr by auto
        next
          case False
          then have sameACC:"accessStore locs (Memory st) = accessStore locs (Memory st')"
            using nonLocChanged by simp
          then have in3:"(case accessStore locs (Memory st) of None \<Rightarrow> False | Some (MValue v)
    \<Rightarrow> \<exists>val. MCon tp (Memory st) locs \<and> tp = MTValue val \<and> accessTypeStore locs (Memory st) = Some tp
      | Some (MPointer p) \<Rightarrow>
          \<exists>len arr.
             MCon tp (Memory st) p \<and>
             tp = MTArray len arr \<and>
             (\<forall>i<len. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr) )"
            using oldSub in1 sameTy unfolding subPrefixStructuralConsistency_def by fastforce
          then show ?thesis
          proof(cases "accessStore locs (Memory st)")
            case None
            then show ?thesis using in3 sameACC by simp
          next
            case (Some a)
            then show ?thesis
            proof(cases a)
              case (MValue x1)
              then obtain val where " MCon tp (Memory st) locs \<and> tp = MTValue val \<and> accessTypeStore locs (Memory st) = Some tp"
                using in3 Some by auto
              moreover have "MCon tp (Memory st') locs" using sameACC calculation by auto
              ultimately show ?thesis using sameACC Some MValue sameTy
                by (auto split:option.splits)
            next
              case (MPointer x2)
              have accl:"accessTypeStore l (Memory st) = Some (MTArray x t)"
                using lInfo 11 nonLocChanged by auto

              then obtain len arr where s:"MCon tp (Memory st) x2 \<and> tp = MTArray len arr \<and>
                         (\<forall>i<len. accessTypeStore (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr)"
                using Some in3 MPointer by auto
              then have mcM:"MCon tp (Memory st) x2" by auto
              have lTyp:"accessTypeStore l (Memory st) = Some (MTArray x t)"
                using lInfo 11 by simp
              then have "MCon tp (Memory st') x2"
                using cpm2m_singleLChange[OF mcM _ _ _ lTyp mcPNew oldSub]
                  11(4) accl s lOrigin nonLocChanged by auto
              moreover have "(\<forall>i<len. accessTypeStore (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr)"
                using s sameTy by simp

              ultimately show ?thesis using Some MPointer sameACC sameTy s
                by (auto split:option.splits)
            qed
          qed
        qed
      qed

    next

      have old:"(\<forall>locs. (\<exists>t. accessStore locs (Memory st) = Some t) = (\<exists>tt. accessTypeStore locs (Memory st) = Some tt))"
        using 2(1) unfolding TypeSafe_def SomeValSomeTyp_def by blast
      have sameACCT:"\<forall>locs. accessTypeStore locs (Memory st) = accessTypeStore locs (Memory st')"
        using 11 lInfo unfolding accessTypeStore_def updateStore_def by auto

      show "SomeValSomeTyp (Memory st')"unfolding SomeValSomeTyp_def
      proof intros
        fix locs
        show "(\<exists>t. accessStore locs (Memory st') = Some t) = (\<exists>tt. accessTypeStore locs (Memory st') = Some tt) "
        proof(cases "locs = l")
          case True
          then have acc:"accessStore l (Memory st') = Some (MPointer p)"
            using 11 by simp
          then have "\<exists>v. accessStore l (Memory st) = Some v" using lOrigin by auto
          then have "\<exists>t. accessTypeStore l (Memory st) = Some t"
            using 2(1) unfolding TypeSafe_def SomeValSomeTyp_def by simp
          then show ?thesis using acc sameACCT True by simp
        next
          case False
          then show ?thesis using old sameACCT nonLocChanged by simp
        qed
      qed
    next
      fix locs t
      assume a1:"accessTypeStore locs (Memory st) = Some t"
      have old:"(\<forall>locs. (\<exists>t. accessStore locs (Memory st) = Some t) = (\<exists>tt. accessTypeStore locs (Memory st) = Some tt))"
        using 2(1) unfolding TypeSafe_def SomeValSomeTyp_def by blast
      have sameACCT:"\<forall>locs. accessTypeStore locs (Memory st) = accessTypeStore locs (Memory st')"
        using 11 lInfo unfolding accessTypeStore_def updateStore_def by auto

      show "accessTypeStore locs (Memory st') = Some t"
      proof(cases "locs = l")
        case True
        then have "\<exists>t. accessTypeStore l (Memory st) = Some t"
          using 2(1) a1 unfolding TypeSafe_def SomeValSomeTyp_def by simp
        then show ?thesis using sameACCT True a1 by simp
      next
        case False
        then show ?thesis using old sameACCT nonLocChanged a1 by simp
      qed
    next
      show "\<And>locs v. accessStore locs (Memory st) = Some (MPointer v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MPointer v')"
        using accL nonLocChanged by auto
    next
      show "\<And>locs v. accessStore locs (Memory st) = Some (MValue v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MValue v')"
        by (metis memoryvalue.distinct(1) lOrigin nonLocChanged option.inject)
    next
      show " \<And>i loc. i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<Longrightarrow> accessStore loc
          (Memory st) = None \<Longrightarrow> accessStore loc (Memory st') = None"
        by (metis lOrigin nonLocChanged option.distinct(1))
    next
      have a12:"Toploc (Memory st) = Toploc (Memory st')" using 11 unfolding updateStore_def by auto
      then show "Toploc (Memory st) \<le> Toploc (Memory st')" by simp
    qed
  qed
qed

text \<open>Assignment case 12: a storage array assigned to a memory variable on the stack: the array is copied into fresh memory.\<close>

lemma TypeSafe_Assign_12:
  assumes "TypeSafe env (Accounts st) (Stack st) (Memory st) (Storage st) cd"
    and "stmt (ASSIGN lv ex) env cd st = Normal ((), st')"
    and "fullyInitialised env (Accounts st) (Stack st)"
    and "expr ex env cd (st\<lparr>state.Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>) (state.Gas st - costs (ASSIGN lv
        ex) env cd st) = Normal ((KStoptr p, type.Storage (STArray x t)), g)"
    and "lexp lv env cd (st\<lparr>state.Gas := g\<rparr>) g = Normal((LStackloc l, type.Memory t'),g')"
    and "cps2mTypeCompatible (STArray x t) t'"
    and "accessStore l (Stack st) = Some (KMemptr p')"
    and "st'' = updateStore l (KMemptr (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))) (Stack st)"
    and "cps2m p (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) x t (Storage st (Address env)) (snd (allocate(Memory st))) = Some m"
    and "st' = st\<lparr>state.Gas := g', Memory := m, Stack := st''\<rparr>"
  shows "StateInvariant env st st' cd"
proof -
  let ?case = "StateInvariant env st st' cd"
  note 2 = assms(1-3)
  note 12 = assms(4-10)
  have nonChangedStack:"\<forall>loc. loc \<noteq> l \<longrightarrow> accessStore loc (Stack st) = accessStore loc (Stack st')" using 12 unfolding accessStore_def updateStore_def by auto
  have accessLStack:"accessStore l (Stack st') = Some (KMemptr (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))))" using 12 unfolding accessStore_def updateStore_def by auto
  have sameStorage:"Storage st' = Storage st " using 12 by auto
  have lInDen:"(type.Memory t', Stackloc l) |\<in>| fmran (Denvalue env)" using lexpStackloc_imps_inDen[of lv env cd] 12(2) by simp
  have nonLocChanged:"\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow> accessStore locs (snd (allocate (Memory st))) = accessStore locs m"
    using 12(6) unfolding cps2m_def using cps2mSingleChange[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t "(Storage st (Address env))" "(snd (allocate (Memory st)))" x m]
    by simp
  have a30:"\<forall>locs. locs \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> \<not> TypedStoSubpref locs
      (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (STArray x t) \<longrightarrow> accessStore locs (snd (allocate (Memory st))) =
      accessStore locs m"
    using 12(6) unfolding cps2m_def using cps2mSingleChange_typedPref[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t "(Storage st
        (Address env))" "(snd (allocate (Memory st)))" x m] by fastforce
  have selfPoint:"\<forall>l l'. l \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> TypedStoSubpref l
      (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (STArray x t) \<and> accessStore l m = Some (MPointer l') \<longrightarrow> l'
      = l"
    using 12(6) unfolding cps2m_def using cps2mSelfPointers[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t "(Storage st (Address env))" " (snd (allocate (Memory st)))" x m ] by blast
  have mInStd:"m = Memory st'" using 12 by simp

  obtain memArr where memArrDef: "t' = MTArray x memArr" using 12(3) cps2mTypeCompatible.simps
    by (metis mtypes.exhaust)

  have p'MCon:"MCon t' (Memory st) p'" using 2 12(4) unfolding TypeSafe_def typeCompat_def using lInDen by (auto split:denvalue.splits option.splits stackvalue.splits type.splits)

  have MConsrc:"SCon (STArray x t) (extractValueType (KStoptr p)) (Storage (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd
      st\<rparr>) (Address env)) \<and> (\<exists>xx. KStoptr p = KStoptr xx)"
    using 2(1) 12(1) exprTypeconInduct(3)[of ex env cd "(st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)"
        "(state.Gas st - costs (ASSIGN lv ex) env cd st)" "KStoptr p" "type.Storage (STArray x t)" g]

    using 2(3) unfolding fullyInitialised_def
    by (auto split:type.splits if_splits )
  have "(\<exists>p. accessStore p' (Memory st) = Some (MPointer p)) \<or> accessStore p' (Memory st) = None" using p'MCon 12(3,4,5)
    using cps2mTypeCompatible.elims(2) by fastforce

  note limitSt1 = TypeSafe_memory_bounds(1)[OF 2(1)]
  note limitSt = TypeSafe_memory_bounds(2)[OF 2(1)]
  moreover have allocateSame:"\<forall>loc. accessStore loc (Memory st) = accessStore loc (snd (allocate (Memory st)))" using allocateSameAccess by blast
  ultimately have "accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (snd (allocate (Memory st))) = None" using LSubPrefL2_def by auto
  then have MCondest:"MCon (MTArray x memArr) m (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" using 12(6,3) unfolding cps2m_def
    using cps2m[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t "(Storage st (Address env))" " (snd (allocate (Memory st)))"
        x m memArr] MConsrc extractValueType.simps(2) memArrDef by simp
  have selfPoint2:"\<forall>l l'. LSubPrefL2 l (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> accessStore l (Memory st') =
      Some (MPointer l') \<longrightarrow> l' = l" using selfPoint limitSt1 limitSt
      "12"(6) a30 cpm2m_iter_dest_unchanged allocateSameAccess cpm2m_def eq_imp_le hash_inequality not_Some_eq
    by (metis cps2mAccessPrePost cps2m_def mInStd)

  have stackDenvalLimits:"\<forall>struct loc stloc. (type.Memory struct, Stackloc loc) |\<in>| fmran (Denvalue env)
                            \<and> accessStore loc (Stack st) = Some (KMemptr stloc) \<longrightarrow> \<not> LSubPrefL2 stloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))"
    using typeSafe_noDenElementOverToploc_mem[OF 2(1)] by auto

  have noC:"\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow> accessStore locs (Memory st) = accessStore locs (Memory st')"
    using allocateSameAccess nonLocChanged mInStd by metis
  have cc:"\<forall>locs. \<not> TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) t' \<longrightarrow> accessStore locs (Memory st) = accessStore locs (Memory st')"
    using a30 mInStd compatible_TypedStoSubpref_imps_TypedMemSubPref[OF 12(3)] allocateSameAccess
    by (metis (no_types, lifting) "12"(6) cps2mSingleChange cps2m_def)

  show ?thesis unfolding TypeSafe_def StateInvariant_def
  proof intros
    show "AddressTypes (Accounts st')" using 2(1) 12 unfolding TypeSafe_def by simp
  next
    show "unique_locations (Denvalue env)" using 2(1) unfolding TypeSafe_def by simp
  next
    have a0:" compPointers (Stack st) (Denvalue env)" using 2(1) unfolding TypeSafe_def by blast
    show "compPointers (Stack st') (Denvalue env)"
      using compPointers_stack_update[OF a0 nonChangedStack accessLStack] .
  next
    show "safeContract (Accounts st') (Storage st')" using sameStorage using 12 2(1) unfolding TypeSafe_def safeContract_def by auto
  next
    show "balanceTypes (Accounts st')" using 12 using 2(1) unfolding TypeSafe_def by simp
  next
    have "envAddressesWellFormed env" using 2(1) unfolding TypeSafe_def by simp
    then show "addressFormat (Address env)" and "addressFormat (Sender env)" by simp+
  next
    show "svalueTypes (Svalue env)" using 2(1) unfolding TypeSafe_def by simp
  next
    have *:"((\<forall>tloc loc. Toploc (Stack st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Stack st) = None) \<and>
              (\<forall>loc y. accessStore loc (Stack st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Stack st). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))) "
      using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by simp
    have **:"Toploc (Stack st) = Toploc (Stack st')" using 12 unfolding updateStore_def by auto
    show "lessThanTopLocs (Stack st')" unfolding lessThanTopLocs_def
    proof intros

      fix tloc loc
      assume h1:"Toploc (Stack st') \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
      then have "Toploc (Stack st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)" using ** by simp
      then show "accessStore loc (Stack st') = None" using *
        by (metis "12"(4) nonChangedStack not_None_eq)
    next
      fix loc y
      assume h1:" accessStore loc (Stack st') = Some y"
      then show "\<exists>tloc<Toploc (Stack st'). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)" using ** *
        by (metis "12"(4) nonChangedStack)
    qed
  next
    show "lessThanTopLocs cd" using 2(1) unfolding TypeSafe_def by simp
  next
    have a10:"Toploc (snd (allocate (Memory st))) = Toploc m" using cps2mTopLocSame 12(6) mInStd unfolding cps2m_def by blast
    have a15:"lessThanTopLocs (Memory st)" using 2 unfolding TypeSafe_def by simp

    have a30: "\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow> accessStore locs (Memory st) = accessStore locs m" using nonLocChanged
      by (metis allocateSameAccess)
    have tloc:"Toploc (Memory st) < Toploc (snd (allocate (Memory st)))" unfolding allocate_def by simp
    show "lessThanTopLocs (Memory st')" unfolding lessThanTopLocs_def
    proof intros
      fix tloc loc
      assume b10: "Toploc (Memory st') \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
      then have b20:"Toploc (Memory st) \<le> tloc" using a10 tloc mInStd by simp
      have "\<not>LSubPrefL2 loc p'"
      proof(rule ccontr)
        assume c10:"\<not> \<not> LSubPrefL2 loc p'"
        then have c20: "LSubPrefL2 loc p'" by simp
        then have c30:"LSubPrefL2 p' (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)" using b10 MemLSubPrefTransitive by auto
        then show False
        proof -
          have "MCon t' (Memory st) p'" using 12(4) 2(1) unfolding TypeSafe_def typeCompat_def using lInDen by fastforce
          then obtain x i where c40: "accessStore p' (Memory st) = Some x \<or> accessStore (hash p' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some x" using MCon_imps_Some by blast
          then show ?thesis
          proof(cases "accessStore p' (Memory st) = Some x")
            case True
            then show ?thesis using lessThanSome_imps_Locs[OF a15 True c30] b20 by simp
          next
            case False
            then have "accessStore (hash p' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some x" using c40 by simp
            then show ?thesis using lessThanSome_imps_Locs_hash c30 a15 b20 by fastforce
          qed
        qed
      qed
      then show "accessStore loc (Memory st') = None " using b10 b20 nonLocChanged a10 mInStd a15 a30
        by (metis (no_types, lifting) LSubPrefL2_def MemLSubPrefTransitive antisym_conv2 hash_inequality hash_suffixes_associative hashesIntSame lessThanTopLocs_def order_less_le_trans tloc)

    next
      fix loc y
      assume "accessStore loc (Memory st') = Some y "
      then show "\<exists>tloc<Toploc (Memory st'). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
        by (metis a10 a15 a30 lessThanTopLocs_def order_less_trans mInStd tloc)
    qed
  next
    show ns:"typeCompat (Denvalue env) (Stack st') (Memory st') (Storage st' (Address env)) cd"
      unfolding typeCompat_def
    proof intros
      fix t'' l'
      assume inDen:" (t'', l') |\<in>| fmran (Denvalue env)"
      show " denvalueCon (Stack st') (Memory st') (Storage st' (Address env)) cd t'' l'"
      proof(cases l')
        case (Stackloc x1)
        then obtain a where adef:"accessStore x1 (Stack st') = Some a" using inDen Stackloc 2(1) unfolding TypeSafe_def typeCompat_def using accessLStack nonChangedStack by fastforce
        then show ?thesis
        proof(cases "a")
          case (KValue x1)
          then show ?thesis using Stackloc adef inDen Stackloc 2(1) accessLStack nonChangedStack unfolding TypeSafe_def typeCompat_def
            by (metis (no_types, lifting) denvalue.simps(5) Option.option.simps(5) stackvalue.distinct(3) stackvalue.simps(17) option.inject)
        next
          case (KCDptr x2)
          then show ?thesis using Stackloc adef inDen Stackloc 2(1) accessLStack nonChangedStack unfolding TypeSafe_def typeCompat_def
            by (metis (no_types, lifting) denvalue.simps(5) Option.option.simps(5) stackvalue.distinct(7) stackvalue.simps(18) option.inject)
        next
          case (KMemptr x3)
          then have "\<exists>struct. t'' = type.Memory struct"
          proof(cases "x1 = l")
            case True
            have "accessStore l (Stack st) = Some (KMemptr p')" using 12(4) by simp
            then show ?thesis using Stackloc adef inDen Stackloc 2(1) KMemptr True unfolding TypeSafe_def typeCompat_def by (cases t'';force+)
          next
            case False
            then have "accessStore x1 (Stack st) = accessStore x1 (Stack st')" using accessLStack nonChangedStack by simp
            then show ?thesis using Stackloc adef inDen Stackloc 2(1) KMemptr unfolding TypeSafe_def typeCompat_def by (cases t'';force+)
          qed
          then obtain struct where structdef:"t'' = type.Memory struct" by blast


          have "MCon struct (Memory st') x3"
          proof(cases "x1 = l")
            case True
            then have x3Def:"x3 = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" using 12 KMemptr adef unfolding accessStore_def updateStore_def by auto
            have "(type.Memory struct, Stackloc x1) |\<in>| fmran (Denvalue env)"
              using Stackloc inDen structdef by blast
            then have "t' = struct" using "12"(4) True lInDen 2(1)
              unfolding TypeSafe_def unique_locations_def by auto

            then show ?thesis using memArrDef MCondest 12 Stackloc True inDen lInDen mInStd structdef x3Def unfolding accessStore_def updateStore_def by metis
          next
            case False
            then have "accessStore x1 (Stack st) = accessStore x1 (Stack st')" using accessLStack nonChangedStack by simp
            then have "accessStore x1 (Stack st) = Some (KMemptr x3)" using adef KMemptr by simp
            then have mgh:"MCon struct (Memory st) x3" using inDen KMemptr Stackloc adef structdef 2(1) unfolding TypeSafe_def typeCompat_def by force

            then show ?thesis using originalMConStillMCon[OF mgh limitSt noC] cc mInStd allocateSameAccess by metis
          qed
          then show ?thesis using structdef KMemptr Stackloc adef inDen Stackloc 2(1) unfolding TypeSafe_def by simp

        next
          case (KStoptr x4)
          then show ?thesis using Stackloc adef sameStorage inDen Stackloc KStoptr 2(1) accessLStack nonChangedStack unfolding TypeSafe_def typeCompat_def
            apply(cases t'')
               apply (metis (no_types, lifting) denvalue.simps(5) Option.option.simps(5) stackvalue.simps(20) type.distinct(3) type.simps(17) lInDen old.prod.inject snd_eqD uniqueLocs)
              apply (metis (no_types, lifting) denvalue.simps(5) Option.option.simps(5) stackvalue.simps(20) type.distinct(7) type.simps(18) lInDen old.prod.inject snd_eqD uniqueLocs)

             apply (metis (no_types, lifting) denvalue.simps(5) Option.option.simps(5) stackvalue.distinct(11) stackvalue.simps(20) type.simps(19) option.inject)

            by (metis (no_types, lifting) denvalue.simps(5) Option.option.simps(5) stackvalue.simps(20) type.distinct(11) type.simps(20) lInDen prod.inject snd_conv uniqueLocs)
        qed

        next
        case (Storeloc x2)
        then show ?thesis using sameStorage inDen 2(1) unfolding TypeSafe_def typeCompat_def by (cases t''; force)
      qed
    qed


    next
    have "Accounts st'= Accounts st" using 12 by auto
    then show "fullyInitialised env (Accounts st') (Stack st')" using 2(3) 12 unfolding fullyInitialised_def updateStore_def accessStore_def by auto
    next

    show "denvalueTypeCorrectness env (Stack st') (Memory st')"
        unfolding denvalueTypeCorrectness_def
    proof(intros)
      fix t2 l2 ptr_loc sub_loc
      assume *:"(type.Memory t2, Stackloc l2) |\<in>| fmran (Denvalue env) \<and> accessStore l2 (Stack st') = Some (KMemptr ptr_loc)"

      show "case t2 of
       MTArray len arr \<Rightarrow>
         (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr)
       | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st') = Some (MTValue val)"
      proof(cases "ptr_loc = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))")
        case False
        then have sameACC:"accessStore l2 (Stack st') = accessStore l2 (Stack st)"
            using nonChangedStack * 12(5) unfolding accessStore_def updateStore_def
            by (metis stackvalue.inject(3) accessLStack accessStore_def option.inject)
        then have mcOld:"MCon t2 (Memory st) ptr_loc" using * by (metis 2(1) sameMemTSafe)
        then have old:"(case t2 of
                         MTArray len arr \<Rightarrow>
                           (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr)
                         | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st) = Some (MTValue val))"
            using sameACC 2(1) * TypeSafe_def denvalueTypeCorrectness_def by fastforce

        have inDenvalue:"(type.Memory t2, Stackloc l2) |\<in>| fmran (Denvalue env)" using * by simp
        have lims:"\<not> LSubPrefL2 ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> \<not> LSubPrefL2 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) ptr_loc"
            using typeSafe_noDenElementOverToploc_mem[OF 2(1) inDenvalue] * sameACC False
            using LSubPrefL2_def MemLSubPrefTransitive by metis

        then show ?thesis
        proof(cases t2)
          case (MTArray x11 x12)
          have old':"(\<forall>i<x11. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some x12)" using old MTArray by simp

          have nonLocChanged_TypedSafe:"\<forall>loc. \<not> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))
                                        \<longrightarrow> accessTypeStore loc (Memory st') = accessTypeStore loc (Memory st)"
              using lims mInStd 12(6) unfolding cps2m_def
              by (metis allocateTypeSameAccess cps2mSingleChange_Typed cps2m_def)
          have nonLocChanged_TypedSafe2:"\<forall>loc. \<not> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))
                                        \<longrightarrow> accessStore loc (Memory st') = accessStore loc (Memory st)"
              using lims mInStd 12(6) unfolding cps2m_def
              by (metis allocateSameAccess cps2mSingleChange cps2m_def)
          have "\<forall>i. \<not> LSubPrefL2 (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))"
              using lims Mutual_NonSub_SpecificNonSub by blast
          then have conc0:"\<forall>i<x11. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some x12"
              using old' lims nonLocChanged_TypedSafe by auto
          then show ?thesis using MTArray old lims nonLocChanged_TypedSafe2
              using nonLocChanged_TypedSafe by auto

          next
          case (MTValue x2)
          have "\<not> LSubPrefL2 ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" using lims by simp
          then have "accessTypeStore ptr_loc (Memory st') = accessTypeStore ptr_loc (Memory st)"
              by (metis "12"(6) allocateTypeSameAccess cps2mSingleChange_Typed cps2m_def mInStd)
          then show ?thesis using MTValue old by simp
        qed
        next
        case True
        then have newLocation:"l2 = l \<and> t2 = (MTArray x memArr)"
            using lInDen accessLStack * memArrDef 2(1) "12"(3,5,7) LSubPrefL2_def nonChangedStack snd_eqD typeSafeUnique typeSafe_noDenElementOverToploc_mem
              unique_locations_def
            by (metis Pair_inject type.inject(3))

        then have l2IsL:"l2 = l" using newLocation by simp
        then have conc0:"ptr_loc = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" using * 12(5,7) by auto
        have conc1:"\<forall>i<x. accessTypeStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some memArr"
            using 12(3,6) memArrDef unfolding cps2m_def
            using cps2m_TypeCompChangeIndexs[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t _ "(snd (allocate (Memory st)))" x m]
              mInStd by blast
        show ?thesis using conc1 conc0 newLocation by simp
      qed
    qed
    next
    have old:"subPrefixStructuralConsistency (Memory st)" using 2(1) unfolding TypeSafe_def by simp
    have noC:"\<forall>locs.
   \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<or> locs = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow>
   accessTypeStore locs (Memory st) = accessTypeStore locs (Memory st')"
        by (metis (lifting) "12"(6) allocateTypeSameAccess cps2mSingleChange_Typed cps2m_def mInStd)
    have some:"SomeValSomeTyp (Memory st)" using 2(1) unfolding TypeSafe_def by simp
    have less:"lessThanTopLocs (Memory st)" using 2(1) unfolding TypeSafe_def by simp
    have n:"accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (Memory st) = None" using limitSt
        using \<open>accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (snd (allocate (Memory st))) = None\<close> allocateSame by presburger

    have cc:"\<forall>locs.
     \<not> TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x memArr) \<or> locs = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow>
     accessTypeStore locs (Memory st) = accessTypeStore locs (Memory st')" using memArrDef
        by (metis (lifting) "12"(3,6) allocateTypeSameAccess compatible_TypedStoSubpref_imps_TypedMemSubPref_neg
            cps2mSingleChange_typedPref_typed cps2m_def mInStd noC)
    have tps:"\<forall>destl'.
   TypedMemSubPref destl' (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x memArr) \<longrightarrow>
   (\<exists>stt. CompMemType (Memory st') x memArr stt (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) destl' \<and>
          (case stt of
           MTArray parent_len parent_arr \<Rightarrow>
             \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some parent_arr
           | MTValue pval \<Rightarrow> accessTypeStore destl' (Memory st') = Some (MTValue pval)))"
        using 12(3,6) unfolding cps2m_def
        using cps2m_TypeCompChange[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t _ "(snd (allocate (Memory st)))" x m memArr]
          mInStd memArrDef by blast
    have mc:"MCon (MTArray x memArr) (Memory st') (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))"
        using MCondest mInStd by blast
    have conc1:"\<forall>i<x. accessTypeStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some memArr"
        using 12(3,6) memArrDef unfolding cps2m_def
        using cps2m_TypeCompChangeIndexs[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t _ "(snd (allocate (Memory st)))" x m]
          mInStd by blast

    have noC2:"\<forall>locs.
     \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<or> locs = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow>
     accessStore locs ((Memory st)) = accessStore locs (Memory st')"
        using "12"(6) unfolding cps2m_def
        using cps2mSingleChange[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t "(Storage st (Address env))" "(snd (allocate (Memory st)))" x m]
          mInStd allocateSameAccess by metis
    have nocc2:"\<forall>locs.
     \<not> TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x memArr) \<longrightarrow>
     accessStore locs (Memory st) = accessStore locs (Memory st')"
        using "12"(6) unfolding cps2m_def
        using cps2mSingleChange_typedPref[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t "(Storage st (Address env))" "(snd (allocate (Memory st)))" x m]
          mInStd allocateSameAccess compatible_TypedStoSubpref_imps_TypedMemSubPref[OF 12(3)]
        by (metis memArrDef noC2)

    show "subPrefixStructuralConsistency (Memory st')"
        using cpm2m_subPrefixPersist[OF old n some noC less cc tps mc _ conc1 noC2 nocc2]
        using selfPoint2 typedPrefix_imp_SubPref by blast
    next
    have old:"(\<forall>locs. (\<exists>t. accessStore locs (Memory st) = Some t) = (\<exists>tt. accessTypeStore locs (Memory st) = Some tt))"
        using 2(1) unfolding TypeSafe_def SomeValSomeTyp_def by blast
    have somesome:"\<forall>destl'. TypedMemSubPref destl' (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x memArr)
          \<longrightarrow> (\<exists>t. accessStore destl' m = Some t) = (\<exists>tt. accessTypeStore destl' m = Some tt)"
        using 12(6,3) unfolding cps2m_def
        using cps2m_TypeCompChange_somesome[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t _ "(snd (allocate (Memory st)))" x m]
          compatible_TypedStoSubpref_imps_TypedMemSubPref memArrDef by blast
    have a30T:"\<forall>locs.
     locs \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> \<not> TypedStoSubpref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (STArray x t) \<longrightarrow>
     accessTypeStore locs (snd (allocate (Memory st))) = accessTypeStore locs (Memory st')"
        using 12(6,3) unfolding cps2m_def using cps2mSingleChange_typedPref_typed[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t _ " (snd (allocate (Memory st)))" x m ]
        using mInStd by blast
    then have a30T:"\<forall>locs. \<not> TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x memArr) \<longrightarrow>
     accessTypeStore locs (snd (allocate (Memory st))) = accessTypeStore locs (Memory st')"
        using mInStd allocateTypeSameAccess memArrDef compatible_TypedStoSubpref_imps_TypedMemSubPref[OF 12(3)]
        by (metis "12"(6) cps2mSingleChange_Typed cps2m_def)

    show "SomeValSomeTyp (Memory st')"unfolding SomeValSomeTyp_def
    proof intros
      fix locs
      show "(\<exists>t. accessStore locs (Memory st') = Some t) = (\<exists>tt. accessTypeStore locs (Memory st') = Some tt) "
      proof(cases "TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x memArr)")
        case True
        then have "(\<exists>t. accessStore locs m = Some t) = (\<exists>tt. accessTypeStore locs m = Some tt)"
            using somesome by simp
        then show ?thesis using mInStd by simp
        next
        case False
        then have "accessStore locs (Memory st) = accessStore locs (Memory st')"
            using a30 mInStd allocateSameAccess
            by (metis (mono_tags, lifting) "12"(3,6) compatible_TypedStoSubpref_imps_TypedMemSubPref_neg cps2mSingleChange cps2m_def
                memArrDef)
        moreover have "accessTypeStore locs (Memory st) = accessTypeStore locs (Memory st')"
            using a30T False
            by (metis allocateTypeSameAccess)
        ultimately show ?thesis using old by metis
      qed
    qed
    next
    fix locs tt
    have a30T:"\<forall>locs.
     locs \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> \<not> TypedStoSubpref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (STArray x t) \<longrightarrow>
     accessTypeStore locs (snd (allocate (Memory st))) = accessTypeStore locs (Memory st')"
        using 12(6,3) unfolding cps2m_def using cps2mSingleChange_typedPref_typed[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t _ " (snd (allocate (Memory st)))" x m ]
        using mInStd by blast

    assume a1:"accessTypeStore locs (Memory st) = Some tt"
    then have some:"\<exists>v. accessStore locs (Memory st) = Some v"
        using 2(1) unfolding TypeSafe_def SomeValSomeTyp_def by auto
    show "accessTypeStore locs (Memory st') = Some tt "
    proof(cases "TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x memArr)")
      case True
      then show ?thesis using mInStd a1 some
          by (metis le_refl limitSt option.distinct(1) typedPrefix_imp_SubPref)
      next
      case False

      then have "accessTypeStore locs (Memory st) = accessTypeStore locs (Memory st')"
        using a30T \<open>accessStore \<lfloor>Toploc (state.Memory st)\<rfloor> (snd (allocate (state.Memory st))) = None\<close>
          assms(6) memArrDef some
        by (metis allocateSameAccess allocateTypeSameAccess compatible_TypedStoSubpref_imps_TypedMemSubPref
           option.distinct(1))
      then show ?thesis using a1 by auto
    qed
    next
    show "\<And>locs v. accessStore locs (Memory st) = Some (MPointer v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MPointer v')"
        by (metis allocateSameAccess dual_order.eq_iff limitSt mInStd nonLocChanged not_None_eq)
    next
    show "\<And>locs v. accessStore locs (Memory st) = Some (MValue v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MValue v')"
      using limitSt noC by (metis dual_order.refl option.distinct(1))
    next
    show " \<And>i loc. i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<Longrightarrow> accessStore loc
        (Memory st) = None \<Longrightarrow> accessStore loc (Memory st') = None"
        using allocateSameAccess limitSt mInStd nonLocChanged
        by (metis LSubPrefL2_def MemLSubPrefTransitive hash_flatten_right hash_inequality hashesIntSame nat_neq_iff)
    next
    have tloc:"Toploc (Memory st) < Toploc (snd (allocate (Memory st)))" unfolding allocate_def by simp
    moreover have topLocEq:"Toploc (snd (allocate (Memory st))) = Toploc (Memory st')"
        using cps2mTopLocSame 12(6) cps2m_def mInStd MCondest
        by (metis (no_types, lifting))
    ultimately show "Toploc (Memory st) \<le> Toploc (Memory st')" by simp
  qed
qed

text \<open>Assignment case 13: a storage array assigned to a storage pointer on the stack: the stack now points to the same storage array.\<close>

lemma TypeSafe_Assign_13:
  assumes "TypeSafe env (Accounts st) (Stack st) (Memory st) (Storage st) cd"
    and "stmt (ASSIGN lv ex) env cd st = Normal ((), st')"
    and "fullyInitialised env (Accounts st) (Stack st)"
    and "expr ex env cd (st\<lparr>state.Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>) (state.Gas st - costs (ASSIGN lv
        ex) env cd st) = Normal ((KStoptr p, type.Storage (STArray x t)), g)"
    and "lexp lv env cd (st\<lparr>state.Gas := g\<rparr>) g = Normal((LStackloc l, type.Storage t'),g')"
    and "t' = STArray x t"
    and "st' = st\<lparr>state.Gas := g', Stack := updateStore l (KStoptr p) (Stack st)\<rparr>"
  shows "StateInvariant env st st' cd"
proof -
  let ?case = "StateInvariant env st st' cd"
  note 2 = assms(1-3)
  note 13 = assms(4-7)
  then have stackChanged:"\<forall>l'. l' \<noteq> l \<longrightarrow> accessStore l' (Stack st) = accessStore l' (Stack st')" unfolding updateStore_def accessStore_def by simp
  have t'InDen:"(type.Storage t', Stackloc l) |\<in>| fmran (Denvalue env)" using lexpStackloc_imps_inDen[OF 13(2)] by blast
  then have lDen:"\<forall>t'. (t', Stackloc l) |\<in>| fmran (Denvalue env) \<longrightarrow> t'= (type.Storage (STArray x t))" using 13 2(1) unfolding TypeSafe_def unique_locations_def by auto

  have pOrigin:"SCon (STArray x t) (extractValueType (KStoptr p)) (Storage (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>) (Address env)) \<and>
      (\<exists>xx. KStoptr p = KStoptr xx) \<and>
      (\<exists>stloc tp'' .
          (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue env) \<and>
          (tp'' = (STArray x t) \<and> KStoptr p = KStoptr stloc \<or> extractValueType (KStoptr p) \<noteq> stloc \<and> CompStoType tp'' (STArray x t) stloc (extractValueType (KStoptr p))))"
    using 2(1) 13(1) 2(3) using
      exprTypeconInduct(3)[of ex env cd "(st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)" "(state.Gas st - costs
          (ASSIGN lv ex) env cd st)" "KStoptr p" "type.Storage (STArray x t)" g]
    by (auto split:type.splits if_splits )
  obtain pParent pParentT where
    pOrigin:"SCon (STArray x t) (extractValueType (KStoptr p)) (Storage (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>) (Address env))
        \<and>(type.Storage pParentT, Storeloc pParent) |\<in>| fmran (Denvalue env) \<and>
          (pParentT = (STArray x t) \<and> KStoptr p = KStoptr pParent \<or> extractValueType (KStoptr p) \<noteq> pParent \<and>
              CompStoType pParentT (STArray x t) pParent (extractValueType (KStoptr p)))"
    using pOrigin by auto
  have a0: "compPointers (Stack st) (Denvalue env)" using 2(1) unfolding TypeSafe_def by simp
  then have pParentRelations:"(\<forall>tp2 l2 l2' stl2.
      (type.Storage tp2, l2) |\<in>| fmran (Denvalue env) \<and>

      (l2 = Stackloc l2' \<and> accessStore l2' (Stack (st)) = Some (KStoptr stl2) \<or> l2 = Storeloc stl2) \<longrightarrow>
      (if TypedStoSubpref stl2 pParent pParentT then CompStoType pParentT tp2 pParent stl2 else if TypedStoSubpref pParent stl2 tp2 then CompStoType tp2 pParentT stl2 pParent else True))"
    using compPointers_def pOrigin by blast
  have pSCon:"SCon (STArray x t) (extractValueType (KStoptr p)) (Storage (st) (Address env))" using pOrigin by force

  have pRelations:"(\<forall>tp2 l2 l2' stl2 .
  (type.Storage tp2, l2) |\<in>| fmran (Denvalue env) \<and>
  ((l2 = Stackloc l2' \<and> accessStore l2' (Stack st) = Some(KStoptr stl2)) \<or> (l2 = Storeloc stl2))
   \<longrightarrow>
  (if TypedStoSubpref p stl2 tp2 then CompStoType tp2 (STArray x t) stl2 p
   else if TypedStoSubpref stl2 p (STArray x t) then CompStoType (STArray x t) tp2 p stl2
   else True))"
  proof intros
    fix tp2 l2 l2' stl2
    assume in1:"(type.Storage tp2, l2) |\<in>| fmran (Denvalue env) \<and> (l2 = Stackloc l2' \<and> accessStore l2' (Stack st) = Some (KStoptr stl2) \<or> l2 = Storeloc stl2)"

    show "if TypedStoSubpref p stl2 tp2 then CompStoType tp2 (STArray x t) stl2 p else if TypedStoSubpref stl2 p (STArray x t) then CompStoType (STArray x t) tp2 p stl2 else True"
    proof(cases "l2 = Stackloc l2'")
      case StL2:True
      then have mcStl2:"SCon tp2 stl2 (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using in1 by fastforce

      then have "SCon pParentT pParent (Storage st (Address env))" using pOrigin using 2(1) unfolding TypeSafe_def typeCompat_def by force
      have prnt:" pParentT = STArray x t \<and> KStoptr p = KStoptr pParent \<or> extractValueType (KStoptr p) \<noteq> pParent \<and>
          CompStoType pParentT (STArray x t) pParent (extractValueType (KStoptr p))"
        using pOrigin by simp
      then have comp:"(if TypedStoSubpref stl2 pParent pParentT then CompStoType pParentT tp2 pParent stl2
                    else if TypedStoSubpref pParent stl2 tp2 then CompStoType tp2 pParentT stl2 pParent else True)"
        using pParentRelations in1 StL2 prnt by force
      then show ?thesis
      proof(cases "TypedStoSubpref p stl2 tp2")
        case pToStl2:True

        then show ?thesis
        proof(cases "pParentT = (STArray x t)")
          case True
          then have cc1:"KStoptr p = KStoptr pParent " using prnt
            using comp_stotype_same_type_same_loc by blast
          then have cc2:"TypedStoSubpref pParent stl2 tp2" using pToStl2 by auto
          then have "CompStoType tp2 (STArray x t) stl2 p"
          proof(cases "TypedStoSubpref stl2 pParent pParentT")
            case t2:True
            then show ?thesis using comp
              by (metis CompStoType_sameLoc_sameType stackvalue.inject(4) True cc1 cc2 typedStoSub_imps_negInv)
          next
            case False
            then have "CompStoType tp2 pParentT stl2 pParent" using comp
              by (simp add: cc2)
            then show ?thesis
              using True cc1 by auto
          qed
          then show ?thesis by (simp add: pToStl2)
        next
          case False
          then have cmp:" CompStoType pParentT (STArray x t) pParent p" using prnt by simp
          then have tsp:"TypedStoSubpref p pParent pParentT" using CompStoType_imps_TypedStoSubpref by simp
          then show ?thesis
          proof(cases "TypedStoSubpref stl2 pParent pParentT")
            case True
            then have prntStl2:" CompStoType pParentT tp2 pParent stl2" using comp by simp
            have "CompStoType tp2 (STArray x t) stl2 p " using pToStl2 prntStl2 CompStoType_sharedSub cmp by simp
            then show ?thesis using pToStl2 by simp
          next
            case f1:False
            then show ?thesis
            proof(cases "TypedStoSubpref pParent stl2 tp2")
              case True
              then have "CompStoType tp2 pParentT stl2 pParent" using comp f1 by simp
              then have "CompStoType tp2 (STArray x t) stl2 p" using cmp CompStoType_trns[of tp2 ] by blast
              then show ?thesis using pToStl2 by simp
            next
              case False
              then have "\<not>TypedStoSubpref p stl2 tp2" using f1 cmp tsp NotRelatedPrnt_imps_notRelatedChild[of stl2 pParent pParentT tp2 p] by simp
              then show ?thesis using f1 pToStl2 cmp by simp
            qed
          qed
        qed
      next
        case f1:False
        then show ?thesis
        proof(cases " TypedStoSubpref stl2 p (STArray x t)")
          case stl2ToP:True
          have " CompStoType (STArray x t) tp2 p stl2"
          proof(cases "pParentT = (STArray x t)")
            case True
            then have cc1:"KStoptr p = KStoptr pParent " using prnt
              using comp_stotype_same_type_same_loc by blast
            then have cc2:"TypedStoSubpref stl2 pParent (STArray x t)" using stl2ToP by auto
            then have " CompStoType (STArray x t) tp2 p stl2"
            proof(cases "TypedStoSubpref stl2 pParent pParentT")
              case t2:True
              then have "CompStoType pParentT tp2 pParent stl2" using comp by simp
              then have "CompStoType (STArray x t) tp2 p stl2" using cc1 True by blast
              then show ?thesis by blast
            next
              case False
              then show ?thesis
              proof(cases "TypedStoSubpref pParent stl2 tp2")
                case True
                then have "CompStoType tp2 pParentT stl2 pParent" using comp False by simp
                then show ?thesis using True cc1 f1 by auto
              next
                case f2:False
                then show ?thesis using False True cc2 by blast
              qed
            qed
            then show ?thesis by blast
          next
            case False
            then have cmp:" CompStoType pParentT (STArray x t) pParent p" using prnt by simp
            then have tsp:"TypedStoSubpref p pParent pParentT" using CompStoType_imps_TypedStoSubpref by simp
            then show ?thesis
            proof(cases "TypedStoSubpref stl2 pParent pParentT")
              case True
              then have prntStl2:" CompStoType pParentT tp2 pParent stl2" using comp by simp
              then show ?thesis using CompStoType_sharedSub[OF prntStl2 stl2ToP cmp] by simp
            next
              case f1:False
              then show ?thesis
              proof(cases "TypedStoSubpref pParent stl2 tp2")
                case True
                then have "CompStoType tp2 pParentT stl2 pParent" using comp f1 by simp
                then have "CompStoType tp2 (STArray x t) stl2 p" using cmp CompStoType_trns[of tp2 ] by blast
                then show ?thesis
                  using CompStoType_sameLocNdTyp CompStoType_sharedSub stl2ToP by blast
              next
                case False
                then show ?thesis
                  using NotReachablePrnt_imps_notReachableChild cmp f1 stl2ToP by blast
              qed
            qed
          qed
          then show ?thesis using f1 by (simp )
        next
          case False
          then show ?thesis
            using f1 by auto
        qed
      qed

    next
      case f3:False
      then have StL2:"l2 = Storeloc stl2"
        using in1 by auto

      then have "SCon pParentT pParent (Storage st (Address env))" using pOrigin using 2(1) unfolding TypeSafe_def typeCompat_def by force
      have prnt:" pParentT = STArray x t \<and> KStoptr p = KStoptr pParent \<or> extractValueType (KStoptr p) \<noteq> pParent \<and>
          CompStoType pParentT (STArray x t) pParent (extractValueType (KStoptr p))"
        using pOrigin by simp
      then have comp:"(if TypedStoSubpref stl2 pParent pParentT then CompStoType pParentT tp2 pParent stl2
                    else if TypedStoSubpref pParent stl2 tp2 then CompStoType tp2 pParentT stl2 pParent else True)"
        using pParentRelations in1 StL2 prnt by force
      then show ?thesis
      proof(cases "TypedStoSubpref p stl2 tp2")
        case pToStl2:True

        then show ?thesis
        proof(cases "pParentT = (STArray x t)")
          case True
          then have cc1:"KStoptr p = KStoptr pParent " using prnt
            using comp_stotype_same_type_same_loc by blast
          then have cc2:"TypedStoSubpref pParent stl2 tp2" using pToStl2 by auto
          then have "CompStoType tp2 (STArray x t) stl2 p"
          proof(cases "TypedStoSubpref stl2 pParent pParentT")
            case t2:True
            then show ?thesis using comp
              by (metis CompStoType_sameLoc_sameType stackvalue.inject(4) True cc1 cc2 typedStoSub_imps_negInv)
          next
            case False
            then have "CompStoType tp2 pParentT stl2 pParent" using comp
              by (simp add: cc2)
            then show ?thesis
              using True cc1 by auto
          qed
          then show ?thesis by (simp add: pToStl2)
        next
          case False
          then have cmp:" CompStoType pParentT (STArray x t) pParent p" using prnt by simp
          then have tsp:"TypedStoSubpref p pParent pParentT" using CompStoType_imps_TypedStoSubpref by simp
          then show ?thesis
          proof(cases "TypedStoSubpref stl2 pParent pParentT")
            case True
            then have prntStl2:" CompStoType pParentT tp2 pParent stl2" using comp by simp
            have "CompStoType tp2 (STArray x t) stl2 p " using pToStl2 prntStl2 CompStoType_sharedSub cmp by simp
            then show ?thesis using pToStl2 by simp
          next
            case f1:False
            then show ?thesis
            proof(cases "TypedStoSubpref pParent stl2 tp2")
              case True
              then have "CompStoType tp2 pParentT stl2 pParent" using comp f1 by simp
              then have "CompStoType tp2 (STArray x t) stl2 p" using cmp CompStoType_trns[of tp2 ] by blast
              then show ?thesis using pToStl2 by simp
            next
              case False
              then have "\<not>TypedStoSubpref p stl2 tp2" using f1 cmp tsp NotRelatedPrnt_imps_notRelatedChild[of stl2 pParent pParentT tp2 p] by simp
              then show ?thesis using f1 pToStl2 cmp by simp
            qed
          qed
        qed
      next
        case f1:False
        then show ?thesis
        proof(cases " TypedStoSubpref stl2 p (STArray x t)")
          case stl2ToP:True
          have " CompStoType (STArray x t) tp2 p stl2"
          proof(cases "pParentT = (STArray x t)")
            case True
            then have cc1:"KStoptr p = KStoptr pParent " using prnt
              using comp_stotype_same_type_same_loc by blast
            then have cc2:"TypedStoSubpref stl2 pParent (STArray x t)" using stl2ToP by auto
            then have " CompStoType (STArray x t) tp2 p stl2"
            proof(cases "TypedStoSubpref stl2 pParent pParentT")
              case t2:True
              then have "CompStoType pParentT tp2 pParent stl2" using comp by simp
              then have "CompStoType (STArray x t) tp2 p stl2" using cc1 True by blast
              then show ?thesis by blast
            next
              case False
              then show ?thesis
              proof(cases "TypedStoSubpref pParent stl2 tp2")
                case True
                then have "CompStoType tp2 pParentT stl2 pParent" using comp False by simp
                then show ?thesis using True cc1 f1 by auto
              next
                case f2:False
                then show ?thesis using False True cc2 by blast
              qed
            qed
            then show ?thesis by blast
          next
            case False
            then have cmp:" CompStoType pParentT (STArray x t) pParent p" using prnt by simp
            then have tsp:"TypedStoSubpref p pParent pParentT" using CompStoType_imps_TypedStoSubpref by simp
            then show ?thesis
            proof(cases "TypedStoSubpref stl2 pParent pParentT")
              case True
              then have prntStl2:" CompStoType pParentT tp2 pParent stl2" using comp by simp
              then show ?thesis using CompStoType_sharedSub[OF prntStl2 stl2ToP cmp] by simp
            next
              case f1:False
              then show ?thesis
              proof(cases "TypedStoSubpref pParent stl2 tp2")
                case True
                then have "CompStoType tp2 pParentT stl2 pParent" using comp f1 by simp
                then have "CompStoType tp2 (STArray x t) stl2 p" using cmp CompStoType_trns[of tp2 ] by blast
                then show ?thesis
                  using CompStoType_sameLocNdTyp CompStoType_sharedSub stl2ToP by blast
              next
                case False
                then show ?thesis
                  using NotReachablePrnt_imps_notReachableChild cmp f1 stl2ToP by blast
              qed
            qed
          qed
          then show ?thesis using f1 by (simp )
        next
          case False
          then show ?thesis using f1 by auto
        qed
      qed
    qed
  qed

  have storageSame:"(Storage st' (Address env)) = (Storage st (Address env))" using 13 by simp
  have memorySame:"Memory st = Memory st'" using 13 by simp
  show ?thesis unfolding TypeSafe_def StateInvariant_def
  proof (intros)
    show tcN:"typeCompat (Denvalue env) (Stack st') (Memory st') (Storage st' (Address env)) cd"
      unfolding typeCompat_def
    proof intros
      fix t l' assume a10:"(t, l') |\<in>| fmran (Denvalue env)"
      show "denvalueCon (Stack st') (Memory st') (Storage st' (Address env)) cd t l'"
      proof (split denvalue.split, intros)
        fix loc assume a20:"l' = Stackloc loc"
        show "case accessStore loc (Stack st') of None \<Rightarrow> False
        | Some (KValue val) \<Rightarrow> (case t of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
        | Some (KCDptr stloc) \<Rightarrow> (case t of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
        | Some (KMemptr stloc) \<Rightarrow> (case t of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
        | Some (KStoptr stloc) \<Rightarrow> (case t of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address env)) | _ \<Rightarrow> False)"
        proof (cases "loc = l")
          case False
          show ?thesis
          proof (split option.split, intros)
            assume a30:"accessStore loc (Stack st') = None"
            then have "accessStore loc (Stack st) = None" using 13(4) False by (simp add:stackSingleUpdate)
            then show False using a30 a20 a10 assms TypeSafe_def False 2(1)
              by (metis option.distinct(1) typeSafeLocExists)
          next
            fix x2 assume a30:"accessStore loc (Stack st') = Some x2"
            then have a40:"accessStore loc (Stack st) = Some x2" using 13(4) False by (simp add:stackSingleUpdate)
            then have a50:"(Memory st) = (Memory st')" using 13(4) by simp
            then have a60:"(Storage st) = (Storage st')" using 13(4) by simp
            show "case x2 of KValue val \<Rightarrow> (case t of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False )
                | KCDptr stloc \<Rightarrow> (case t of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
                | KMemptr stloc \<Rightarrow> (case t of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
                | KStoptr stloc \<Rightarrow> (case t of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address env)) | _ \<Rightarrow> False)"
              using a10 a20 a30 a40 a50 a60 2(1) unfolding TypeSafe_def typeCompat_def by (cases x2; cases t; force)
          qed
        next
          case sameLoc:True
          show ?thesis
          proof (split option.split, intros)
            assume a30:"accessStore loc (Stack st') = None"
            then show False using a20 a10 assms(1) sameLoc 13(4) notNoneUpdate[of st' g' loc "(KMemptr p)"] by simp
          next
            fix x2 assume a30:"accessStore loc (Stack st') = Some x2"
            then have x2IsP:"x2 = KStoptr p" using 13 sameLoc by auto
            show "case x2 of KValue val \<Rightarrow> (case t of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False )
            | KCDptr stloc \<Rightarrow> (case t of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
            | KMemptr stloc \<Rightarrow> (case t of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
            | KStoptr stloc \<Rightarrow> (case t of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address env)) | _ \<Rightarrow> False)"
            proof(cases "x2")
              case (KValue x1)

              then show ?thesis using x2IsP by auto
            next
              case (KCDptr x2)
              then show ?thesis using x2IsP by (simp add:sameLoc)
            next
              case (KMemptr x3)
              then show ?thesis using x2IsP by (simp add:sameLoc)
            next
              case (KStoptr x4)
              then show ?thesis using x2IsP a10 a20 lDen storageSame sameLoc
                using pSCon by force
            qed
          qed
        qed
      next
        fix x2 assume a20:"l' = Storeloc x2"
        then have "(Storage st' (Address env)) = (Storage st (Address env))" using 13(4) by simp
        then show "case t of type.Storage typ \<Rightarrow> SCon typ x2 (Storage st' (Address env)) | _ \<Rightarrow> False" using a10 a20 TypeSafe_def 2(1) pSCon a10 a20 lDen storageSame
        proof -
          have "\<And>t d. (t, d) |\<notin>| fmran (Denvalue env) \<or>
                (case d of Stackloc l \<Rightarrow>
                (case accessStore l (Stack st) of None \<Rightarrow> False
                | Some (KValue l) \<Rightarrow> (case t of Value t \<Rightarrow> typeCon t l | _ \<Rightarrow> False)
                | Some (KCDptr l) \<Rightarrow> (case t of Calldata m \<Rightarrow> MCon m cd l | _ \<Rightarrow> False)
                | Some (KMemptr l) \<Rightarrow> (case t of type.Memory m \<Rightarrow> MCon m (Memory st) l | _ \<Rightarrow> False)
                | Some (KStoptr l) \<Rightarrow> (case t of type.Storage s \<Rightarrow> SCon s l (Storage st (Address env)) | _ \<Rightarrow> False))
                | Storeloc l \<Rightarrow> (case t of type.Storage s \<Rightarrow> SCon s l (Storage st (Address env)) | _ \<Rightarrow> False))"
            using 2(1) TypeSafe_def typeCompat_def by auto
          then show ?thesis
            by (metis (no_types) denvalue.simps(6) a10 a20 storageSame)
        qed
      qed
    qed
    have "typeCompat (Denvalue env) (Stack st) (Memory st') (Storage st' (Address env)) cd"
      unfolding typeCompat_def
    proof intros
      fix t l' assume a10:"(t, l') |\<in>| fmran (Denvalue env)"
      show "denvalueCon (Stack st) (Memory st') (Storage st' (Address env)) cd t l' "
      proof(cases l')
        case (Stackloc x1)
        then show ?thesis
        proof(cases "x1 = l")
          case sameLoc:True
          then show ?thesis
          proof (cases "accessStore x1 (Stack st)")
            case None
            then show ?thesis using Stackloc a10 assms(1) sameLoc 13(4)
              by (metis 2(1) option.distinct(1) typeSafeAllStacklocsExist)
          next
            case (Some a)
            then show ?thesis
            proof(cases "a")
              case (KValue x1)
              then show ?thesis using a10 Stackloc Some 2(1) unfolding TypeSafe_def typeCompat_def
                by fastforce
            next
              case (KCDptr x2)
              then show ?thesis using a10 Stackloc Some 2(1) unfolding TypeSafe_def typeCompat_def
                by fastforce
            next
              case (KMemptr x3)
              then show ?thesis using a10 Stackloc Some 2(1) unfolding TypeSafe_def typeCompat_def
                by (metis (lifting) denvalue.simps(5) Option.option.simps(5) stackvalue.simps(19) type.simps(20) sameLoc t'InDen)
            next
              case (KStoptr x4)
              then show ?thesis using a10 Stackloc Some 2(1) unfolding TypeSafe_def typeCompat_def using lDen storageSame sameLoc
                using pSCon by force
            qed
          qed
        next
          case False
          then have "accessStore x1 (Stack st) = accessStore x1 (Stack st')"
            using stackChanged by auto
          then show ?thesis using tcN Stackloc a10 unfolding typeCompat_def by fastforce
        qed
      next
        case (Storeloc x2)
        then show ?thesis using a10 tcN unfolding typeCompat_def by fastforce
      qed
    qed
  next
    show "unique_locations (Denvalue env)" using 2(1) typeSafeUnique by auto
  next
    have "(Accounts st) = Accounts(st')" using 13 by simp
    then show "balanceTypes (Accounts st')" using balanceTypes_def balanceTypes_def 2(1) typeSafeAccounts by simp
  next
    have a0:"compPointers (Stack st)(Denvalue env)" using 2(1) storageSame unfolding TypeSafe_def by simp
    show " compPointers (Stack st') (Denvalue env)" unfolding compPointers_def
    proof(intros)
      fix tp1 tp2 l1 l22 l1' l2' stl1 stl2
      assume a1:"(type.Storage tp1, l1) |\<in>| fmran (Denvalue env) \<and>
   (type.Storage tp2, l22) |\<in>| fmran (Denvalue env) \<and>
   (l1 = Stackloc l1' \<and> accessStore l1' (Stack st') = Some (KStoptr stl1) \<or> l1 = Storeloc stl1) \<and>
   (l22 = Stackloc l2' \<and> accessStore l2' (Stack st') = Some (KStoptr stl2) \<or> l22 = Storeloc stl2)"
      have a2:"(\<forall>x y. x |\<in>| fmran (Denvalue env) \<and> y |\<in>| fmran (Denvalue env) \<and> snd x = snd y \<longrightarrow> x = y)"
        using 2(1) unfolding TypeSafe_def unique_locations_def by simp

      then show "if TypedStoSubpref stl2 stl1 tp1 then CompStoType tp1 tp2 stl1 stl2 else if TypedStoSubpref stl1 stl2 tp2 then CompStoType tp2 tp1 stl2 stl1 else True"
      proof(cases "l1 = Storeloc stl1")
        case t1:True
        then show ?thesis
        proof(cases "l22 = Storeloc stl2")
          case True
          then show ?thesis using t1 a0 a1 unfolding compPointers_def by blast
        next
          case False
          then have a4:"l22 = Stackloc l2' \<and> accessStore l2' (Stack st') = Some (KStoptr stl2)" using a1 by simp
          then show ?thesis
          proof(cases "l2' = l")
            case True
            then have "stl2 = p" using a4 13 by simp
            then show ?thesis using pRelations a1 a0 t1 True a4 lDen by blast
          next
            case False
            then have " accessStore l2' (Stack st') = accessStore l2' (Stack st)" using stackChanged a4 by simp
            then show ?thesis using a0 a1 t1 unfolding compPointers_def by metis
          qed
        qed
      next
        case f1:False
        then have a4:"l1 = Stackloc l1' \<and> accessStore l1' (Stack st') = Some (KStoptr stl1)" using a1 by simp
        then show ?thesis
        proof(cases "l22 = Storeloc stl2")
          case t1:True
          then show ?thesis
          proof(cases "l1' = l")
            case True
            then have "stl1 = p" using a4 13 by simp
            then show ?thesis using pRelations a1 a0 t1 True a4 lDen
              by (metis CompStoType_sameLoc_sameType type.inject(4) typedStoSub_imps_negInv)
          next
            case False
            then have " accessStore l1' (Stack st') = accessStore l1' (Stack st)" using stackChanged a4 by simp
            then show ?thesis using a0 a1 t1 unfolding compPointers_def by metis
          qed
        next
          case False
          then have a4':"l22 = Stackloc l2' \<and> accessStore l2' (Stack st') = Some (KStoptr stl2)" using a1 by simp
          then show ?thesis
          proof(cases "l1' = l")
            case True
            then have p1:"stl1 = p" using a4 13 by simp
            then have tp1c:"tp1 = (STArray x t)" using lDen a1
              using True a4 by auto
            then show ?thesis
            proof(cases "l2' = l")
              case True
              then have p2:"stl2 = p" using a4' 13 by auto
              then have tp2c:"tp2 = STArray x t" using lDen a1 True a4' by auto
              then show ?thesis using p2 p1 tp1c tp2c by auto
            next
              case False
              then have " accessStore l2' (Stack st') = accessStore l2' (Stack st)" using stackChanged a4 by simp
              then show ?thesis
                by (metis CompStoType_sameLoc_sameType a1 p1 pRelations tp1c typedStoSub_imps_negInv)
            qed
          next
            case False
            then have same1:" accessStore l1' (Stack st') = accessStore l1' (Stack st)" using stackChanged a4 by simp
            then show ?thesis
            proof(cases "l2' = l")
              case True
              then have p2:"stl2 = p" using a4' 13 by auto
              then have tp2c:"tp2 = STArray x t" using lDen a1 True a4' by auto
              then show ?thesis using same1 pRelations p2 tp2c a1
                by metis
            next
              case False
              then have " accessStore l2' (Stack st') = accessStore l2' (Stack st)" using stackChanged a4 by simp
              then show ?thesis using a1 a0 same1
                using compPointers_def by auto
            qed
          qed
        qed
      qed
    qed
  next
    show "svalueTypes (Svalue env)" using svalueTypes_def typeSafeSvalue 2(1) by simp
  next
    have "(Storage st') = (Storage st)" using 13(4) by simp
    then show "safeContract (Accounts st') (Storage st')" using 2(1) 13 unfolding safeContract_def TypeSafe_def by auto
  next
    have a10:"Toploc (Stack st') = Toploc (Stack st)" using 13(4) unfolding updateStore_def by simp
    then have a20:"\<exists>val. accessStore l (Stack st) = Some val" using t'InDen typeSafeLocExists 2(1) TypeSafe_def by blast
    then have a30:"(\<forall>tloc loc. Toploc (Stack st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Stack st) = None)
                 \<and>(\<forall>loc y. accessStore loc (Stack st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Stack st). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))"
      using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by simp
    then have a40:"(\<forall>tloc loc. Toploc (Stack st') \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Stack st) = None)
                  \<and>(\<forall>loc y. accessStore loc (Stack st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Stack st'). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))"
      using a10 by simp
    show "lessThanTopLocs (Stack st')" unfolding lessThanTopLocs_def
    proof intros
      fix tloc loc
      assume *:"Toploc (Stack st') \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
      then show "accessStore loc (Stack st') = None"
      proof(cases "loc = l")
        case True
        then show ?thesis using * a10
          by (metis a20 a30 option.distinct(1))
      next
        case False
        then have a50:"accessStore loc (Stack st) = accessStore loc (Stack st')" using 13(4) unfolding updateStore_def accessStore_def by simp
        then show ?thesis using 2(1) a40 * a10 False a30 by simp
      qed
    next
      fix loc y
      assume *:" accessStore loc (Stack st') = Some y "
      show "\<exists>tloc<Toploc (Stack st'). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
      proof(cases "loc = l")
        case True
        then show ?thesis using *a10 a20 a30 by simp
      next
        case False
        then have a50:"accessStore loc (Stack st) = accessStore loc (Stack st')" using 13(4) unfolding updateStore_def accessStore_def by simp
        then show ?thesis using * 2(1) a40 by simp
      qed
    qed
  next
    show "lessThanTopLocs cd" using 2(1) unfolding TypeSafe_def using 13 by auto
  next
    show "lessThanTopLocs (Memory st')" using 2(1) unfolding TypeSafe_def using 13 by auto
  next
    have "envAddressesWellFormed env" using 2(1) unfolding TypeSafe_def by auto
    then show "addressFormat (Address env)" and "addressFormat (Sender env)" by simp+
  next
    show "AddressTypes (Accounts st')" using 2(1) unfolding TypeSafe_def using 13 by simp
  next
    have accSame:"Accounts st'= Accounts st" using 13 by auto
    from 2(3) obtain c_fi ct_fi dud_fi where fi:"
         Type (Accounts st (Address env)) = Some (atype.Contract c_fi) \<and>
         Contract env = c_fi \<and>
         ep $$ c_fi = Some (ct_fi, dud_fi) \<and>
         (\<forall>id v. (ct_fi $$ id = Some (Var v)) = (Denvalue env $$ id = Some (type.Storage v, Storeloc id))) \<and>
         (\<forall>id v loc. Denvalue env $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc) \<and>
         (\<forall>t0 l0 p0.
             (type.Storage t0, Stackloc l0) |\<in>| fmran (Denvalue env) \<and> accessStore l0 (Stack st) = Some (KStoptr p0) \<longrightarrow>
             (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue env) \<and> CompStoType t' t0 l' p0))"
      unfolding fullyInitialised_def by blast
    have fiPtrs':"\<forall>t'' l'' p''.
             (type.Storage t'', Stackloc l'') |\<in>| fmran (Denvalue env) \<and> accessStore l'' (Stack st') = Some (KStoptr p'') \<longrightarrow>
             (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue env) \<and> CompStoType t' t'' l' p'')"
    proof (intro allI impI)
      fix t'' l'' p''
      assume in1:"(type.Storage t'', Stackloc l'') |\<in>| fmran (Denvalue env) \<and> accessStore l'' (Stack st') = Some (KStoptr p'')"
      then show "\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue env) \<and> CompStoType t' t'' l' p''"
      proof(cases "l'' = l")
        case True
        then have isST:"t'' = STArray x t" using in1 lDen by blast
        then have isP:"p'' = p" using 13(4) in1 True unfolding accessStore_def updateStore_def by simp
        then have "\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue env) \<and> CompStoType t' (STArray x t) l' p"
          using pOrigin isST isP by force
        then show ?thesis by (simp add: isP isST)
      next
        case False
        then have sameAcc:"accessStore l'' (Stack st') =accessStore l'' (Stack st)"
          by (simp add: stackChanged)
        then show ?thesis using fi in1 by presburger
      qed
    qed
    show "fullyInitialised env (Accounts st') (Stack st')"
      unfolding fullyInitialised_def using fi fiPtrs' accSame by metis
  next
    have inDen:"(type.Storage t', Stackloc l) |\<in>| fmran (Denvalue env)" using t'InDen by simp
    have denAc:"(\<forall>t l. (t, l) |\<in>| fmran (Denvalue env) \<longrightarrow>
         (denvalueCon (Stack st) (Memory st) (Storage st (Address env)) cd t l))" using 2(1) unfolding TypeSafe_def typeCompat_def by simp
    have isVal:"\<exists>val. accessStore l (Stack st) = Some (KStoptr val)"
    proof(cases "accessStore l (Stack st)")
      case None
      then show ?thesis using inDen denAc by fastforce
    next
      case (Some a)
      then show ?thesis
      proof(cases a)
        case (KValue x1)
        then show ?thesis using inDen denAc Some by fastforce
      next
        case (KCDptr x2)
        then show ?thesis using inDen denAc Some by fastforce
      next
        case (KMemptr x3)
        then show ?thesis using inDen denAc Some by fastforce
      next
        case (KStoptr x4)
        then show ?thesis using inDen denAc Some by simp
      qed
    qed

    have memSame:"Memory st = Memory st'" using 13(4) by simp
    have cc0:"\<forall>l ptr. (accessStore l (Stack st) = Some (KMemptr ptr)) = (accessStore l (Stack st') = Some (KMemptr ptr))"
    proof intros
      fix l2 ptr
      show " (accessStore l2 (Stack st) = Some (KMemptr ptr)) = (accessStore l2 (Stack st') = Some (KMemptr ptr)) "
      proof
        assume *:"accessStore l2 (Stack st) = Some (KMemptr ptr)"
        then have "l \<noteq> l2" using isVal by auto
        then show "accessStore l2 (Stack st') = Some (KMemptr ptr)"
          using 13(4) * unfolding updateStore_def accessStore_def by auto
      next
        assume *:"accessStore l2 (Stack st') = Some (KMemptr ptr)"
        then have "l \<noteq> l2" using 13(4) by auto
        then show "accessStore l2 (Stack st) = Some (KMemptr ptr) "
          using * 13(4) unfolding updateStore_def accessStore_def by simp
      qed
    qed
  next
    have cc0:"\<forall>l ptr_loc. accessStore l (Stack st') = Some (KMemptr ptr_loc) \<longrightarrow> accessStore l (Stack st) = Some (KMemptr ptr_loc)"
      using 13(4) unfolding updateStore_def accessStore_def by auto
    show "denvalueTypeCorrectness env (Stack st') (Memory st')"

      unfolding denvalueTypeCorrectness_def
    proof intros
      fix t l ptr_loc sub_loc
      assume "(type.Memory t, Stackloc l) |\<in>| fmran (Denvalue env) \<and>
     accessStore l (Stack st') = Some (KMemptr ptr_loc)"
      then have "(case t of
       MTArray len arr \<Rightarrow>
         (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr)
       | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st) = Some (MTValue val))"
        using 2(1) unfolding TypeSafe_def denvalueTypeCorrectness_def using cc0 by blast
      moreover have "Memory st = Memory st'" using 13(4) by simp
      ultimately show "case t of
     MTArray len arr \<Rightarrow>
       (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr)
     | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st') = Some (MTValue val)"
        by metis
    qed
  next
    show "subPrefixStructuralConsistency (Memory st')"
      using 2(1) unfolding TypeSafe_def using 13(4) by simp
  next
    show "SomeValSomeTyp (Memory st')" using 2(1) unfolding TypeSafe_def using 13(4) by simp
  next
    show "\<And>locs t. accessTypeStore locs (Memory st) = Some t \<Longrightarrow> accessTypeStore locs (Memory st') = Some t"
      using 2(1) unfolding TypeSafe_def using 13(4) by simp
  next
    show "\<And>locs v. accessStore locs (Memory st) = Some (MPointer v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MPointer v')"
      using 13(4) by simp
  next
    show "\<And>locs v. accessStore locs (Memory st) = Some (MValue v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MValue v')"
      using 13(4) by simp
  next
    show " \<And>i loc. i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<Longrightarrow> accessStore loc
        (Memory st) = None \<Longrightarrow> accessStore loc (Memory st') = None"
      using 13(4) by simp
  next
    show "Toploc (Memory st) \<le> Toploc (Memory st')" using 13(4) by simp
  qed
qed

text \<open>Assignment case 14: a storage array assigned to a storage location: the array is copied within storage.\<close>

lemma TypeSafe_Assign_14:
  assumes "TypeSafe env (Accounts st) (Stack st) (Memory st) (Storage st) cd"
    and "stmt (ASSIGN lv ex) env cd st = Normal ((), st')"
    and "fullyInitialised env (Accounts st) (Stack st)"
    and "expr ex env cd (st\<lparr>state.Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>) (state.Gas st - costs (ASSIGN lv
        ex) env cd st) = Normal ((KStoptr p, type.Storage (STArray x t)), g)"
    and "lexp lv env cd (st\<lparr>state.Gas := g\<rparr>) g = Normal((LStoreloc l, type.Storage t'),g')"
    and "t' = (STArray x t)"
    and "copy p l x t (Storage st (Address env)) = Some s"
    and "st' = st\<lparr>state.Gas := g', Storage := (Storage st) (Address env := s)\<rparr>"
  shows "StateInvariant env st st' cd"
proof -
  let ?case = "StateInvariant env st st' cd"
  note 2 = assms(1-3)
  note 14 = assms(4-8)
  have sameStack:"(Stack st) = (Stack st')" using 14 unfolding accessStore_def updateStore_def by auto
  have sameMemory:"Memory st' = Memory st " using 14 by auto
  have nonLocChanged:"\<forall>t' locs. \<not> LSubPrefL2 locs l \<or> locs = l \<longrightarrow> accessStorage t' locs (Storage st (Address env)) = accessStorage t' locs s"
    using 14(4) unfolding copy_def using copySingleChange[of p l t "(Storage st (Address env))" x s]
    by fastforce
  have a30:"\<forall>locs t''. \<not> TypedStoSubpref locs l (STArray x t) \<longrightarrow> accessStorage t'' locs (Storage st (Address env)) = accessStorage t'' locs s"
    using 14(4) unfolding copy_def using copySingleChange_typedPref[of p l t "(Storage st (Address env))" x s] by simp
  then have a35:"\<forall>locs t''. locs \<noteq> l \<and> \<not> TypedStoSubpref locs l (STArray x t) \<longrightarrow>
     accessStorage t'' locs (Storage st (Address env)) = accessStorage t'' locs (Storage st' (Address env))"
    using 14 by auto
  have mInStd:"s = Storage st' (Address env)" using 14 by simp

  obtain stloc tp'' where MConsrc:"SCon (STArray x t) (extractValueType (KStoptr p)) (Storage (st\<lparr>Gas := state.Gas st - costs
      (ASSIGN lv ex) env cd st\<rparr>) (Address env)) \<and> (\<exists>xx. KStoptr p = KStoptr xx) \<and>

          (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue env) \<and>
          (tp'' = (STArray x t) \<and> KStoptr p = KStoptr stloc \<or> extractValueType (KStoptr p) \<noteq> stloc \<and> CompStoType tp'' (STArray x t) stloc (extractValueType (KStoptr p)))"
    using 2(1) 14(1) exprTypeconInduct(3)[of ex env cd "(st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)"
        "(state.Gas st - costs (ASSIGN lv ex) env cd st)" "KStoptr p" "type.Storage (STArray x t)" g]
    using 2(3)
    by (auto split:type.splits if_splits )

  note limitSt1 = TypeSafe_memory_bounds(1)[OF 2(1)]
  note limitSt = TypeSafe_memory_bounds(2)[OF 2(1)]
  moreover have allocateSame:"\<forall>loc. accessStore loc (Memory st) = accessStore loc (snd (allocate (Memory st)))" using allocateSameAccess by blast
  ultimately have "accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (snd (allocate (Memory st))) = None" using LSubPrefL2_def by auto

  have stackDenvalLimits:"\<forall>struct loc stloc. (type.Memory struct, Stackloc loc) |\<in>| fmran (Denvalue env)
                          \<and> accessStore loc (Stack st) = Some (KMemptr stloc) \<longrightarrow> \<not> LSubPrefL2 stloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))"
    using typeSafe_noDenElementOverToploc_mem[OF 2(1)] by auto

  show ?thesis unfolding TypeSafe_def StateInvariant_def
  proof intros
    show "AddressTypes (Accounts st')" using 2(1) 14 unfolding TypeSafe_def by simp
  next
    show "unique_locations (Denvalue env)" using 2(1) unfolding TypeSafe_def by simp
  next
    have a0:" compPointers (Stack st) (Denvalue env)" using 2(1) unfolding TypeSafe_def by blast
    show "compPointers (Stack st') (Denvalue env)" unfolding compPointers_def
    proof(intros)
      fix tp1 tp2 l1 l2 l1' l2' stl1 stl2
      assume a1:"(type.Storage tp1, l1) |\<in>| fmran (Denvalue env) \<and>
     (type.Storage tp2, l2) |\<in>| fmran (Denvalue env) \<and>
     (l1 = Stackloc l1' \<and> accessStore l1' (Stack st') = Some (KStoptr stl1) \<or> l1 = Storeloc stl1) \<and> (l2 = Stackloc l2'
         \<and> accessStore l2' (Stack st') = Some (KStoptr stl2) \<or> l2 = Storeloc stl2)"
      then show " if TypedStoSubpref stl2 stl1 tp1 then CompStoType tp1 tp2 stl1 stl2 else if TypedStoSubpref stl1 stl2 tp2 then CompStoType tp2 tp1 stl2 stl1 else True"
      proof(cases "TypedStoSubpref stl2 stl1 tp1")
        case True
        then show ?thesis using a1 sameStack a0 unfolding compPointers_def by simp
      next
        case f1:False
        then show ?thesis
        proof(cases "TypedStoSubpref stl1 stl2 tp2")
          case True
          then show ?thesis using a1 sameStack a0 unfolding compPointers_def by simp
        next
          case False
          then show ?thesis using f1 by simp
        qed
      qed
    qed
  next
    have scOld:"safeContract (Accounts st) (Storage st)" using 2(1) unfolding TypeSafe_def by simp
    show "safeContract (Accounts st') (Storage st')" unfolding safeContract_def
    proof intros
      fix e ct dud i tp
      assume *:"Type (Accounts st' (Address (e::environment))) = Some (atype.Contract (Contract e)) \<and>
               ep $$ Contract (e::environment) = Some (ct, dud) \<and>
               ct $$ i = Some (Var tp)"
      show "SCon tp i (Storage st' (Address e))"
      proof (cases "Address e = Address env")
        case False
        then have sameAddr:"Storage st' (Address e) = Storage st (Address e)" using 14 by simp
        moreover have "SCon tp i (Storage st (Address e))"
          using * scOld 14 unfolding safeContract_def by fastforce
        ultimately show ?thesis by simp
      next
        case addrEq:True
        have typedOld:"Type (Accounts st (Address e)) = Some (atype.Contract (Contract e))"
          using * 14 by simp
        have epOld:"ep $$ Contract e = Some (ct, dud)"
          using * by simp
        have ctOld:"ct $$ i = Some (Var tp)"
          using * by simp
        have denI:"Denvalue env $$ i = Some (type.Storage tp, Storeloc i)"
          using fi_contract_var_to_denvalue_storeloc[OF 2(3) addrEq typedOld epOld ctOld] .
        have inDenI:"(type.Storage tp, Storeloc i) |\<in>| fmran (Denvalue env)"
          using denI by (simp add: fmranI)
        have oldSConE:"SCon tp i (Storage st (Address e))"
          using scOld typedOld epOld ctOld unfolding safeContract_def by blast
        have oldSCon:"SCon tp i (Storage st (Address env))"
          using oldSConE addrEq by simp
        have newSCon:"SCon tp i (Storage st' (Address env))"
        proof(cases rule:lexpStorageG[OF 2(1) 14(2) 2(3)])
          case lInDen:1
          have cmpStoPtr:"(
            (type.Storage tp, l') |\<in>| fmran (Denvalue env) \<and>
            (type.Storage (STArray x t), Storeloc l) |\<in>| fmran (Denvalue env) \<and>
             l' = Storeloc i)
             \<longrightarrow>
            (if TypedStoSubpref l i tp then CompStoType tp (STArray x t) i l
             else if TypedStoSubpref i l (STArray x t) then CompStoType (STArray x t) tp l i else True)"
            using 2(1) 14(3) lInDen inDenI unfolding TypeSafe_def compPointers_def by blast
          then have cmpStoPtr2:"(if TypedStoSubpref l i tp then CompStoType tp (STArray x t) i l
             else if TypedStoSubpref i l (STArray x t) then CompStoType (STArray x t) tp l i else True)"
            using 14(3) lInDen inDenI sameStack
            using 2(1) compPointers_def typeSafeCompPointers by blast

          have h7:"SCon (STArray x t) l (Storage st (Address env))" using 2(1) 14 lInDen
              sameStoLocTSafe by blast
          have p:"((if TypedStoSubpref stloc l t' then CompStoType t' tp'' l stloc
             else if TypedStoSubpref l stloc tp'' then CompStoType tp'' t' stloc l else True))"
            using 2(1) unfolding TypeSafe_def compPointers_def using lInDen MConsrc by blast
          have denSub:"(if TypedStoSubpref stloc l (STArray x t) then CompStoType (STArray x t) tp'' l stloc
             else if TypedStoSubpref l stloc tp'' then CompStoType tp'' (STArray x t) stloc l else True)"
            using p 14(3) by blast
          have paInf:"(tp'' = (STArray x t) \<and> KStoptr p = KStoptr stloc
                  \<or> extractValueType (KStoptr p) \<noteq> stloc \<and> CompStoType tp'' (STArray x t) stloc (extractValueType (KStoptr p)))"
            using MConsrc by simp
          have h8:"SCon (STArray x t) p (Storage st (Address env))" using MConsrc by simp
          have rel:"CompStoType t' (STArray x t) l l"
            using 14(3) CompStoType_sameLocNdTyp by simp
          have SCondest:"SCon (STArray x t) l s"
            using copy_dest_scon_from_rel[OF 14(4) 14(3) h7 h8 denSub paInf ] by auto
          then have SCondest2:"SCon (STArray x t) l (Storage st' (Address env))"
            by (simp add: mInStd)
          then have SCondest3:"SCon t' l (Storage st' (Address env))" using 14(3)
            by (simp add: mInStd )
          show ?thesis
          proof(cases "TypedStoSubpref l i tp")
            case True
            then have "CompStoType tp (STArray x t) i l"
              by (simp add: cmpStoPtr2)
            then show ?thesis using SCondest2 oldSCon a35 TypedStoSubpref_shared_parent_related SCon_sub_imps_Parent
              by blast
          next
            case f1:False
            then show ?thesis
            proof(cases "TypedStoSubpref i l (STArray x t)")
              case True
              then have "CompStoType t' tp l i " using cmpStoPtr2 f1 14(3) by simp
              then show ?thesis using SCondest3 SCon_imps_sublocs by blast
            next
              case False
              have notSame:"i \<noteq> l" using False by auto
              have k7:"\<forall>locs. TypedStoSubpref locs i tp \<longrightarrow> locs \<noteq> l " using f1 by blast
              have k8:"\<forall>locs. TypedStoSubpref locs l (STArray x t) \<longrightarrow> locs \<noteq> i" using False by auto
              show ?thesis using sublocs_nonchanged_SCon[OF f1 a35 oldSCon False] by blast
            qed
          qed
        next
          case sub2:(2 l''' t''')
          have cmpStoPtr:"(
              (type.Storage tp, Storeloc i) |\<in>| fmran (Denvalue env) \<and>
              (type.Storage t''', Storeloc l''') |\<in>| fmran (Denvalue env) )
               \<longrightarrow>
              (if TypedStoSubpref l''' i tp then CompStoType tp t''' i l'''
               else if TypedStoSubpref i l''' t''' then CompStoType t''' tp l''' i else True)"
            using 2(1) 14(3) inDenI unfolding TypeSafe_def compPointers_def by blast
          then have cmpStoPtr2:"(if TypedStoSubpref l''' i tp then CompStoType tp t''' i l'''
               else if TypedStoSubpref i l''' t''' then CompStoType t''' tp l''' i else True)"
            using 14(3) sub2 inDenI sameStack by auto

          have scl''':"SCon t''' l''' (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using sub2 by fastforce
          then have h7:"SCon (STArray x t) l (Storage st (Address env))" using 2(1) 14 sameStoLocTSafe sub2
            using SCon_imps_sublocs by blast
          have p:"((if TypedStoSubpref stloc l''' t''' then CompStoType t''' tp'' l''' stloc
               else if TypedStoSubpref l''' stloc tp'' then CompStoType tp'' t''' stloc l''' else True))"
            using 2(1) unfolding TypeSafe_def compPointers_def using sub2 MConsrc by blast
          have denSub:"(if TypedStoSubpref stloc l''' t''' then CompStoType t''' tp'' l''' stloc
             else if TypedStoSubpref l''' stloc tp'' then CompStoType tp'' t''' stloc l''' else True)"
            using p 14(3) by blast
          have paInf:"(tp'' = (STArray x t) \<and> KStoptr p = KStoptr stloc
                  \<or> extractValueType (KStoptr p) \<noteq> stloc \<and> CompStoType tp'' (STArray x t) stloc (extractValueType (KStoptr p)))"
            using MConsrc by simp
          have h8:"SCon (STArray x t) p (Storage st (Address env))" using MConsrc by simp
          have rel:"CompStoType t''' (STArray x t) l''' l" using sub2 14(3) by auto
          have SCondest:"SCon (STArray x t) l s"
            using copy_dest_scon_from_rel[OF 14(4) 14(3) h7 h8 denSub paInf rel] .
          then have SCondest2:"SCon (STArray x t) l (Storage st' (Address env))"
            by (simp add: mInStd)
          then have SCondest3:"SCon t' l (Storage st' (Address env))" using 14(3)
            by (simp add: mInStd )
          show ?thesis
          proof(cases "TypedStoSubpref l''' i tp")
            case True
            then have "CompStoType tp t''' i l'''" using cmpStoPtr2 by simp
            then have "CompStoType tp (STArray x t) i l" using sub2 using CompStoType_trns 14(3) by blast
            then show ?thesis using SCondest2 oldSCon a35 14(3) TypedStoSubpref_shared_parent_related SCon_sub_imps_Parent
              by blast
          next
            case f1:False
            then show ?thesis
            proof(cases "TypedStoSubpref i l''' t'''")
              case True
              then have "l''' \<noteq> i" using f1 using TypedStoSubpref_sameLoc by auto
              then show ?thesis
              proof(cases "l = i")
                case t5:True
                then have "CompStoType t''' tp l''' i" using cmpStoPtr2 f1 14(3) True by simp
                moreover have "CompStoType t''' t' l''' i" using t5 sub2 by auto
                ultimately have "t' = tp" using CompStoType_sameLocs_sameType by simp
                then show ?thesis using SCondest3 SCon_imps_sublocs t5 by simp
              next
                case False
                then have "CompStoType t''' tp l''' i" using cmpStoPtr2 f1 14(3) True by simp
                then show ?thesis
                proof(cases "CompStoType t' tp l i")
                  case True
                  then show ?thesis using SCon_imps_sublocs SCondest3 by blast
                next
                  case False
                  then show ?thesis
                    using SCon_imps_sublocs SCon_sub_imps_Parent SCondest2 \<open>CompStoType t''' tp l''' i\<close> a35 scl''' sub2(2) 14(3) by blast
                qed
              qed
            next
              case False
              then have asm10:"\<not> TypedStoSubpref l i tp" using NotRelatedPrnt_imps_notRelatedChild[OF False f1] sub2 by blast
              then have asm20:"\<not> TypedStoSubpref i l t'" using sub2 NotReachablePrnt_imps_notReachableChild False f1 by blast
              have notSame:"i \<noteq> l" using False sub2 by blast
              have k7:"\<forall>locs. TypedStoSubpref locs i tp \<longrightarrow> locs \<noteq> l " using f1 sub2 asm10 asm20 by blast
              have k8:"\<forall>locs. TypedStoSubpref locs l (STArray x t) \<longrightarrow> locs \<noteq> i" using False sub2 14(3) asm10 asm20 by blast
              show ?thesis using sublocs_nonchanged_SCon[OF _ a35 oldSCon] asm10 asm20 14(3) by blast
            qed
          qed
        next
          case sub3:(3 l''' t''' l'''')
          have cmpStoPtr:"(
              (type.Storage tp, Storeloc i) |\<in>| fmran (Denvalue env) \<and>
              (type.Storage t''', Stackloc l'''') |\<in>| fmran (Denvalue env) \<and>
               accessStore l'''' (Stack st) = Some (KStoptr l'''))
               \<longrightarrow>
              (if TypedStoSubpref l''' i tp then CompStoType tp t''' i l'''
               else if TypedStoSubpref i l''' t''' then CompStoType t''' tp l''' i else True)"
            using 2(1) 14(3) inDenI unfolding TypeSafe_def compPointers_def by blast
          then have cmpStoPtr2:"(if TypedStoSubpref l''' i tp then CompStoType tp t''' i l'''
               else if TypedStoSubpref i l''' t''' then CompStoType t''' tp l''' i else True)"
            using 14(3) sub3 inDenI sameStack by auto

          have scl''':"SCon t''' l''' (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using sub3 by fastforce
          then have h7:"SCon (STArray x t) l (Storage st (Address env))" using 2(1) 14 sameStoLocTSafe sub3
            using SCon_imps_sublocs by blast
          have p:"(
              (if TypedStoSubpref stloc l''' t''' then CompStoType t''' tp'' l''' stloc
               else if TypedStoSubpref l''' stloc tp'' then CompStoType tp'' t''' stloc l''' else True))"
            using 2(1) unfolding TypeSafe_def compPointers_def using sub3 MConsrc by blast
          have denSub:"(if TypedStoSubpref stloc l''' t''' then CompStoType t''' tp'' l''' stloc
             else if TypedStoSubpref l''' stloc tp'' then CompStoType tp'' t''' stloc l''' else True)"
            using p 14(3) by blast
          have paInf:"(tp'' = (STArray x t) \<and> KStoptr p = KStoptr stloc
                  \<or> extractValueType (KStoptr p) \<noteq> stloc \<and> CompStoType tp'' (STArray x t) stloc (extractValueType (KStoptr p)))"
            using MConsrc by simp
          have h8:"SCon (STArray x t) p (Storage st (Address env))" using MConsrc by simp
          have rel:"CompStoType t''' (STArray x t) l''' l" using sub3 14(3) by auto
          have SCondest:"SCon (STArray x t) l s"
            using copy_dest_scon_from_rel[OF 14(4) 14(3) h7 h8 denSub paInf rel] .
          then have SCondest2:"SCon (STArray x t) l (Storage st' (Address env))"
            by (simp add: mInStd)
          then have SCondest3:"SCon t' l (Storage st' (Address env))" using 14(3)
            by (simp add: mInStd )
          show ?thesis
          proof(cases "TypedStoSubpref l''' i tp")
            case True
            then have "CompStoType tp t''' i l'''" using cmpStoPtr2 by simp
            then have "CompStoType tp (STArray x t) i l" using sub3 using CompStoType_trns 14(3) by blast
            then show ?thesis using SCondest2 oldSCon a35 14(3) TypedStoSubpref_shared_parent_related SCon_sub_imps_Parent
              by blast
          next
            case f1:False
            then show ?thesis
            proof(cases "TypedStoSubpref i l''' t'''")
              case True
              then have "l''' \<noteq> i" using f1 using TypedStoSubpref_sameLoc by auto
              then show ?thesis
              proof(cases "l = i") case t5:True
                then have "CompStoType t''' tp l''' i" using cmpStoPtr2 f1 14(3) True by simp
                moreover have "CompStoType t''' t' l''' i" using t5 sub3 by auto
                ultimately have "t' = tp" using CompStoType_sameLocs_sameType by simp
                then show ?thesis using SCondest3 SCon_imps_sublocs t5 by simp
              next
                case False
                then have "CompStoType t''' tp l''' i" using cmpStoPtr2 f1 14(3) True by simp
                then show ?thesis
                proof(cases "CompStoType t' tp l i")
                  case True
                  then show ?thesis using SCon_imps_sublocs SCondest3 by blast
                next
                  case False
                  then show ?thesis
                    using SCon_imps_sublocs SCon_sub_imps_Parent SCondest2 \<open>CompStoType t''' tp l''' i\<close> a35 scl''' sub3(3) 14(3) by blast
                qed
              qed
            next
              case False
              then have asm10:"\<not> TypedStoSubpref l i tp" using NotRelatedPrnt_imps_notRelatedChild[OF False f1] sub3 by blast
              then have asm20:"\<not> TypedStoSubpref i l t'" using sub3 NotReachablePrnt_imps_notReachableChild False f1 by blast
              have notSame:"i \<noteq> l" using False sub3 by blast
              have k7:"\<forall>locs. TypedStoSubpref locs i tp \<longrightarrow> locs \<noteq> l " using f1 sub3 asm10 asm20 by blast
              have k8:"\<forall>locs. TypedStoSubpref locs l (STArray x t) \<longrightarrow> locs \<noteq> i" using False sub3 14(3) asm10 asm20 by blast
              show ?thesis using sublocs_nonchanged_SCon[OF _ a35 oldSCon] asm10 asm20 14(3) by blast
            qed
          qed
        qed
        then show ?thesis using newSCon addrEq by simp

      qed
    qed
  next
    show "balanceTypes (Accounts st')" using 14 using 2(1) unfolding TypeSafe_def by simp
  next
    have "envAddressesWellFormed env" using 2(1) unfolding TypeSafe_def by simp
    then show "addressFormat (Address env)" and "addressFormat (Sender env)" by simp+
  next
    show "svalueTypes (Svalue env)" using 2(1) unfolding TypeSafe_def by simp
  next
    have *:"((\<forall>tloc loc. Toploc (Stack st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Stack st) = None) \<and>
            (\<forall>loc y. accessStore loc (Stack st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Stack st). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))) "
      using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by simp
    have **:"Toploc (Stack st) = Toploc (Stack st')" using 14 unfolding updateStore_def by auto
    show "lessThanTopLocs (Stack st')" using sameStack * ** unfolding lessThanTopLocs_def by auto
  next
    show "lessThanTopLocs cd" using 2(1) unfolding TypeSafe_def by simp
  next
    show "lessThanTopLocs (Memory st')" using sameMemory unfolding lessThanTopLocs_def
      by (simp add: limitSt limitSt1)
  next
    show "typeCompat (Denvalue env) (Stack st') (Memory st') (Storage st' (Address env)) cd"
      unfolding typeCompat_def
    proof intros
      fix t'' l'
      assume inDen:" (t'', l') |\<in>| fmran (Denvalue env)"

      show " denvalueCon (Stack st') (Memory st') (Storage st' (Address env)) cd t'' l'"
      proof(cases l')
        case (Stackloc x1)
        then obtain a where adef:"accessStore x1 (Stack st') = Some a" using inDen Stackloc 2(1) unfolding TypeSafe_def typeCompat_def using sameStack by fastforce
        then show ?thesis
        proof(cases "a")
          case (KValue x1)
          then show ?thesis using Stackloc adef inDen Stackloc 2(1) sameStack unfolding TypeSafe_def typeCompat_def
            by (metis (no_types, lifting) denvalue.simps(5) Option.option.simps(5) stackvalue.simps(17) )
        next
          case (KCDptr x2)
          then show ?thesis using Stackloc adef inDen Stackloc 2(1) sameStack unfolding TypeSafe_def typeCompat_def
            by (metis (no_types, lifting) denvalue.simps(5) Option.option.simps(5) stackvalue.simps(18))
        next
          case (KMemptr x3)
          then show ?thesis using Stackloc adef inDen Stackloc 2(1) sameStack sameMemory unfolding TypeSafe_def typeCompat_def by (cases t''; fastforce)
        next
          case (KStoptr x4)
          then obtain struct where structDef: "t'' = type.Storage struct" using Stackloc adef inDen Stackloc 2(1) sameStack unfolding TypeSafe_def typeCompat_def
            by (cases t''; fastforce)

          have "SCon struct x4 (Storage st' (Address env))"
          proof(cases rule:lexpStorageG[OF 2(1) 14(2) 2(3)])
            case lInDen:1
            then have h7:"SCon (STArray x t) l (Storage st (Address env))" using 2(1) 14
                sameStoLocTSafe by blast

            have p:"((if TypedStoSubpref stloc l t' then CompStoType t' tp'' l stloc
               else if TypedStoSubpref l stloc tp'' then CompStoType tp'' t' stloc l else True))"
              using 2(1) unfolding TypeSafe_def compPointers_def using lInDen MConsrc by blast

            have denSub:"(if TypedStoSubpref stloc l (STArray x t) then CompStoType (STArray x t) tp'' l stloc
               else if TypedStoSubpref l stloc tp'' then CompStoType tp'' (STArray x t) stloc l else True)"
              using p 14(3) by blast
            have paInf:"(tp'' = (STArray x t) \<and> KStoptr p = KStoptr stloc
                  \<or> extractValueType (KStoptr p) \<noteq> stloc \<and> CompStoType tp'' (STArray x t) stloc (extractValueType (KStoptr p)))"
              using MConsrc by simp
            have h8:"SCon (STArray x t) p (Storage st (Address env))" using MConsrc by simp
            have rel:"CompStoType t' (STArray x t) l l"
              using 14(3) CompStoType_sameLocNdTyp by simp
            have SCondest:"SCon (STArray x t) l s"
              using copy_dest_scon_from_rel[OF 14(4) 14(3) h7 h8 denSub paInf] by simp

            then have SCondest2:"SCon (STArray x t) l (Storage st' (Address env))"
              by (simp add: mInStd)
            then have SCondest3:"SCon t' l (Storage st' (Address env))" using 14(3)
              by (simp add: mInStd )

            have cmpStoPtr:"(
              (type.Storage struct, l') |\<in>| fmran (Denvalue env) \<and>
              (type.Storage (STArray x t), Storeloc l) |\<in>| fmran (Denvalue env) \<and>
               l' = Stackloc x1 \<and> accessStore x1 (Stack st) = Some (KStoptr x4))
               \<longrightarrow>
              (if TypedStoSubpref l x4 struct then CompStoType struct (STArray x t) x4 l
               else if TypedStoSubpref x4 l (STArray x t) then CompStoType (STArray x t) struct l x4 else True)"
              using 2(1) 14(3) lInDen inDen adef Stackloc KStoptr structDef unfolding TypeSafe_def compPointers_def by blast

            then have cmpStoPtr2:"(if TypedStoSubpref l x4 struct then CompStoType struct (STArray x t) x4 l
               else if TypedStoSubpref x4 l (STArray x t) then CompStoType (STArray x t) struct l x4 else True)"
              using 14(3) lInDen inDen adef Stackloc KStoptr structDef sameStack by auto

            have SConx4Old:"SCon struct x4 (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using adef Stackloc KStoptr inDen 2(1) sameStack structDef
              by fastforce

            have "SCon struct x4 (Storage st' (Address env))"
            proof(cases "TypedStoSubpref l x4 struct")
              case True
              then have "CompStoType struct (STArray x t) x4 l" using cmpStoPtr2 by simp
              then show ?thesis using SCondest2 SConx4Old a35 14(3) TypedStoSubpref_shared_parent_related SCon_sub_imps_Parent
                by blast
            next
              case f1:False
              then show ?thesis
              proof(cases "TypedStoSubpref x4 l (STArray x t)")
                case True
                then have "CompStoType t' struct l x4 " using cmpStoPtr2 f1 14(3) by simp
                then show ?thesis using SCondest3 SCon_imps_sublocs by blast
              next
                case False
                have notSame:"x4 \<noteq> l" using False by auto
                have k7:"\<forall>locs. TypedStoSubpref locs x4 struct \<longrightarrow> locs \<noteq> l " using f1 by blast
                have k8:"\<forall>locs. TypedStoSubpref locs l (STArray x t) \<longrightarrow> locs \<noteq> x4" using False by auto
                show ?thesis using sublocs_nonchanged_SCon[OF f1 a35 SConx4Old False] by blast
              qed
            qed
            then show ?thesis by simp
          next
            case sub2:(2 l''' t''')
            have cmpStoPtr:"(
              (type.Storage struct, l') |\<in>| fmran (Denvalue env) \<and>
              (type.Storage t''', Storeloc l''') |\<in>| fmran (Denvalue env) \<and>
               l' = Stackloc x1 \<and> accessStore x1 (Stack st) = Some (KStoptr x4))
               \<longrightarrow>
              (if TypedStoSubpref l''' x4 struct then CompStoType struct t''' x4 l'''
               else if TypedStoSubpref x4 l''' t''' then CompStoType t''' struct l''' x4 else True)"
              using 2(1) 14(3) inDen adef Stackloc KStoptr structDef unfolding TypeSafe_def compPointers_def by blast

            then have cmpStoPtr2:"(if TypedStoSubpref l''' x4 struct then CompStoType struct t''' x4 l'''
               else if TypedStoSubpref x4 l''' t''' then CompStoType t''' struct l''' x4 else True)"
              using 14(3) sub2 inDen adef Stackloc KStoptr structDef sameStack by auto

            have SConx4Old:"SCon struct x4 (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using adef Stackloc KStoptr inDen 2(1) sameStack structDef
              by fastforce
            have scl''':"SCon t''' l''' (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using sub2 by fastforce

            then have h7:"SCon (STArray x t) l (Storage st (Address env))" using 2(1) 14
                sameStoLocTSafe sub2
              using SCon_imps_sublocs by blast

            have p:"(
              (if TypedStoSubpref stloc l''' t''' then CompStoType t''' tp'' l''' stloc
               else if TypedStoSubpref l''' stloc tp'' then CompStoType tp'' t''' stloc l''' else True))"
              using 2(1) unfolding TypeSafe_def compPointers_def using sub2 MConsrc by blast

            have denSub:"(if TypedStoSubpref stloc l''' t''' then CompStoType t''' tp'' l''' stloc
               else if TypedStoSubpref l''' stloc tp'' then CompStoType tp'' t''' stloc l''' else True)"
              using p 14(3) by blast
            have paInf:"(tp'' = (STArray x t) \<and> KStoptr p = KStoptr stloc
                  \<or> extractValueType (KStoptr p) \<noteq> stloc \<and> CompStoType tp'' (STArray x t) stloc (extractValueType (KStoptr p)))"
              using MConsrc by simp
            have h8:"SCon (STArray x t) p (Storage st (Address env))" using MConsrc by simp
            have rel:"CompStoType t''' (STArray x t) l''' l" using sub2 14(3) by auto
            have SCondest:"SCon (STArray x t) l s"
              using copy_dest_scon_from_rel[OF 14(4) 14(3) h7 h8 denSub paInf rel] .
            then have SCondest2:"SCon (STArray x t) l (Storage st' (Address env))"
              by (simp add: mInStd)
            then have SCondest3:"SCon t' l (Storage st' (Address env))" using 14(3)
              by (simp add: mInStd )

            have "SCon struct x4 (Storage st' (Address env))"
            proof(cases "TypedStoSubpref l''' x4 struct")
              case True
              then have "CompStoType struct t''' x4 l'''" using cmpStoPtr2 by simp
              then have "CompStoType struct (STArray x t) x4 l" using sub2
                using CompStoType_trns 14(3) by blast
              then show ?thesis using SConx4Old a35 14(3) TypedStoSubpref_shared_parent_related SCon_sub_imps_Parent SCondest2 by blast
            next
              case f1:False
              then show ?thesis
              proof(cases "TypedStoSubpref x4 l''' t")
                case True
                then have "l''' \<noteq> x4" using f1
                  using TypedStoSubpref_sameLoc by auto
                then show ?thesis
                proof(cases "l = x4")
                  case t5:True
                  then have " CompStoType t''' struct l''' x4" using cmpStoPtr2 f1 14(3) True
                    using sub2(2) by auto
                  moreover have "CompStoType t''' t' l''' x4" using t5 sub2 by auto
                  ultimately have "t' = struct" using CompStoType_sameLocs_sameType
                    by simp
                  then show ?thesis using SCondest3 SCon_imps_sublocs t5 by simp
                next
                  case False
                  then show ?thesis
                  proof(cases "CompStoType t' struct l x4 ")
                    case True
                    then show ?thesis
                      using SCon_imps_sublocs SCondest3 by blast
                  next
                    case False
                    then show ?thesis
                      using SCon_preserved_array_update[OF rel cmpStoPtr2 f1 SCondest2 SConx4Old a35] by blast
                  qed
                qed
              next
                case False
                show ?thesis using sublocs_nonchanged_SCon[OF _ a35 SConx4Old] 14(3)
                  using SCon_preserved_array_update[OF rel cmpStoPtr2 f1 SCondest2 SConx4Old a35] by blast
              qed
            qed
            then show ?thesis by simp
          next
            case sub3:(3 l''' t''' l'''')
            have cmpStoPtr:"(
              (type.Storage struct, l') |\<in>| fmran (Denvalue env) \<and>
              (type.Storage t''', Stackloc l'''') |\<in>| fmran (Denvalue env) \<and>
               l' = Stackloc x1 \<and> accessStore x1 (Stack st) = Some (KStoptr x4)) \<and> accessStore l'''' (Stack st) = Some (KStoptr l''')
               \<longrightarrow>
              (if TypedStoSubpref l''' x4 struct then CompStoType struct t''' x4 l'''
               else if TypedStoSubpref x4 l''' t''' then CompStoType t''' struct l''' x4 else True)"
              using 2(1) 14(3) inDen adef Stackloc KStoptr structDef unfolding TypeSafe_def compPointers_def by blast

            then have cmpStoPtr2:"(if TypedStoSubpref l''' x4 struct then CompStoType struct t''' x4 l'''
               else if TypedStoSubpref x4 l''' t''' then CompStoType t''' struct l''' x4 else True)"
              using 14(3) sub3 inDen adef Stackloc KStoptr structDef sameStack by auto

            have SConx4Old:"SCon struct x4 (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using adef Stackloc KStoptr inDen 2(1) sameStack structDef
              by fastforce
            have scl''':"SCon t''' l''' (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using sub3 by fastforce

            then have h7:"SCon (STArray x t) l (Storage st (Address env))" using 2(1) 14
                sameStoLocTSafe sub3
              using SCon_imps_sublocs by blast

            have p:"((if TypedStoSubpref stloc l''' t''' then CompStoType t''' tp'' l''' stloc
               else if TypedStoSubpref l''' stloc tp'' then CompStoType tp'' t''' stloc l''' else True))"
              using 2(1) unfolding TypeSafe_def compPointers_def using sub3 MConsrc by blast

            have denSub:"(if TypedStoSubpref stloc l''' t''' then CompStoType t''' tp'' l''' stloc
               else if TypedStoSubpref l''' stloc tp'' then CompStoType tp'' t''' stloc l''' else True)"
              using p 14(3) by blast
            have paInf:"(tp'' = (STArray x t) \<and> KStoptr p = KStoptr stloc
                  \<or> extractValueType (KStoptr p) \<noteq> stloc \<and> CompStoType tp'' (STArray x t) stloc (extractValueType (KStoptr p)))"
              using MConsrc by simp
            have h8:"SCon (STArray x t) p (Storage st (Address env))" using MConsrc by simp
            have rel:"CompStoType t''' (STArray x t) l''' l" using sub3 14(3) by auto
            have SCondest:"SCon (STArray x t) l s"
              using copy_dest_scon_from_rel[OF 14(4) 14(3) h7 h8 denSub paInf rel] .
            then have SCondest2:"SCon (STArray x t) l (Storage st' (Address env))"
              by (simp add: mInStd)
            then have SCondest3:"SCon t' l (Storage st' (Address env))" using 14(3)
              by (simp add: mInStd )

            have "SCon struct x4 (Storage st' (Address env))"
            proof(cases "TypedStoSubpref l''' x4 struct")
              case True
              then have "CompStoType struct t''' x4 l'''" using cmpStoPtr2 by simp
              then have "CompStoType struct (STArray x t) x4 l" using sub3
                using CompStoType_trns 14(3) by blast
              then show ?thesis using SCondest2 SConx4Old a35 14(3) TypedStoSubpref_shared_parent_related SCon_sub_imps_Parent
                by blast
            next
              case f1:False
              then show ?thesis
              proof(cases "TypedStoSubpref x4 l''' t'''")
                case True
                then have "l''' \<noteq> x4" using f1
                  using TypedStoSubpref_sameLoc by auto
                then show ?thesis
                proof(cases "l = x4")
                  case t5:True
                  then have " CompStoType t''' struct l''' x4" using cmpStoPtr2 f1 14(3) True by simp
                  moreover have "CompStoType t''' t' l''' x4" using t5 sub3 by auto
                  ultimately have "t' = struct" using CompStoType_sameLocs_sameType
                    by simp
                  then show ?thesis using SCondest3 SCon_imps_sublocs t5 by simp
                next
                  case False
                  then have " CompStoType t''' struct l''' x4" using cmpStoPtr2 f1 14(3) True by simp
                  then show ?thesis
                  proof(cases "CompStoType t' struct l x4 ")
                    case True
                    then show ?thesis
                      using SCon_imps_sublocs SCondest3 by blast
                  next
                    case False
                    then show ?thesis
                      using SCon_imps_sublocs SCon_sub_imps_Parent SCondest2 \<open>CompStoType t''' struct l''' x4\<close> a35 scl''' sub3(3) 14(3) by blast
                  qed
                qed
              next
                case False
                then have asm10:"\<not> TypedStoSubpref l x4 struct" using NotRelatedPrnt_imps_notRelatedChild[OF False f1 ] sub3 by blast
                then have asm20:"\<not> TypedStoSubpref x4 l t'" using sub3 NotReachablePrnt_imps_notReachableChild False f1 by blast
                have notSame:"x4 \<noteq> l" using False sub3 by blast
                have k7:"\<forall>locs. TypedStoSubpref locs x4 struct \<longrightarrow> locs \<noteq> l " using f1 sub3 asm10 asm20 by blast
                have k8:"\<forall>locs. TypedStoSubpref locs l (STArray x t) \<longrightarrow> locs \<noteq> x4" using False sub3 14(3) asm10 asm20 by blast
                show ?thesis using sublocs_nonchanged_SCon[OF _ a35 SConx4Old] asm10 asm20 14(3) by blast
              qed
            qed
            then show ?thesis by simp
          qed
          then show ?thesis using Stackloc inDen 2(1) sameStack KStoptr adef structDef by simp
        qed
      next
        case (Storeloc x2)
        then obtain struct where structDef: "t'' = type.Storage struct" using Storeloc inDen 2(1) sameStack unfolding TypeSafe_def typeCompat_def
          by (cases t''; fastforce)

        have "SCon struct x2 (Storage st' (Address env))"
        proof(cases rule:lexpStorageG[OF 2(1) 14(2) 2(3)])
          case lInDen:1
          have cmpStoPtr:"(
            (type.Storage struct, l') |\<in>| fmran (Denvalue env) \<and>
            (type.Storage (STArray x t), Storeloc l) |\<in>| fmran (Denvalue env) \<and>
             l' = Storeloc x2)
             \<longrightarrow>
            (if TypedStoSubpref l x2 struct then CompStoType struct (STArray x t) x2 l
             else if TypedStoSubpref x2 l (STArray x t) then CompStoType (STArray x t) struct l x2 else True)"
            using 2(1) 14(3) lInDen inDen Storeloc structDef unfolding TypeSafe_def compPointers_def by blast

          then have cmpStoPtr2:"(if TypedStoSubpref l x2 struct then CompStoType struct (STArray x t) x2 l
             else if TypedStoSubpref x2 l (STArray x t) then CompStoType (STArray x t) struct l x2 else True)"
            using 14(3) lInDen inDen Storeloc structDef sameStack by simp

          have SConx4Old:"SCon struct x2 (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using Storeloc inDen 2(1) sameStack structDef
            by fastforce

          then have h7:"SCon (STArray x t) l (Storage st (Address env))" using 2(1) 14 lInDen
              sameStoLocTSafe by blast

          have p:"((if TypedStoSubpref stloc l t' then CompStoType t' tp'' l stloc
             else if TypedStoSubpref l stloc tp'' then CompStoType tp'' t' stloc l else True))"
            using 2(1) unfolding TypeSafe_def compPointers_def using lInDen MConsrc by blast

          have denSub:"(if TypedStoSubpref stloc l (STArray x t) then CompStoType (STArray x t) tp'' l stloc
             else if TypedStoSubpref l stloc tp'' then CompStoType tp'' (STArray x t) stloc l else True)"
            using p 14(3) by blast
          have paInf:"(tp'' = (STArray x t) \<and> KStoptr p = KStoptr stloc
                  \<or> extractValueType (KStoptr p) \<noteq> stloc \<and> CompStoType tp'' (STArray x t) stloc (extractValueType (KStoptr p)))"
            using MConsrc by simp
          have h8:"SCon (STArray x t) p (Storage st (Address env))" using MConsrc by simp
          have rel:"CompStoType t' (STArray x t) l l"
            using 14(3) CompStoType_sameLocNdTyp by simp
          have SCondest:"SCon (STArray x t) l s"
            using copy_dest_scon_from_rel[OF 14(4) 14(3) h7 h8 denSub paInf ] by simp

          then have SCondest2:"SCon (STArray x t) l (Storage st' (Address env))"
            by (simp add: mInStd)
          then have SCondest3:"SCon t' l (Storage st' (Address env))" using 14(3)
            by (simp add: mInStd )

          have "SCon struct x2 (Storage st' (Address env))"
          proof(cases "TypedStoSubpref l x2 struct")
            case True
            then have "CompStoType struct (STArray x t) x2 l"
              by (simp add: cmpStoPtr2)
            then show ?thesis using SCondest2 SConx4Old a35 TypedStoSubpref_shared_parent_related SCon_sub_imps_Parent
              by blast
          next
            case f1:False
            then show ?thesis
            proof(cases "TypedStoSubpref x2 l (STArray x t)")
              case True
              then have "CompStoType t' struct l x2 " using cmpStoPtr2 f1 14(3) by simp
              then show ?thesis using SCondest3 SCon_imps_sublocs by blast
            next
              case False
              have notSame:"x2 \<noteq> l" using False by auto
              have k7:"\<forall>locs. TypedStoSubpref locs x2 struct \<longrightarrow> locs \<noteq> l " using f1 by blast
              have k8:"\<forall>locs. TypedStoSubpref locs l (STArray x t) \<longrightarrow> locs \<noteq> x2" using False by auto
              show ?thesis using sublocs_nonchanged_SCon[OF f1 a35 SConx4Old False] by blast
            qed
          qed
          then show ?thesis by simp
        next
          case sub2:(2 l''' t''')
          have cmpStoPtr:"(
              (type.Storage struct, Storeloc x2) |\<in>| fmran (Denvalue env) \<and>
              (type.Storage t''', Storeloc l''') |\<in>| fmran (Denvalue env) )
               \<longrightarrow>
              (if TypedStoSubpref l''' x2 struct then CompStoType struct t''' x2 l'''
               else if TypedStoSubpref x2 l''' t''' then CompStoType t''' struct l''' x2 else True)"
            using 2(1) 14(3) inDen Storeloc structDef unfolding TypeSafe_def compPointers_def by blast

          then have cmpStoPtr2:"(if TypedStoSubpref l''' x2 struct then CompStoType struct t''' x2 l'''
               else if TypedStoSubpref x2 l''' t''' then CompStoType t''' struct l''' x2 else True)"
            using 14(3) sub2 inDen Storeloc structDef sameStack by auto

          have SConx4Old:"SCon struct x2 (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using Storeloc inDen 2(1) sameStack structDef
            by fastforce
          have scl''':"SCon t''' l''' (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using sub2 by fastforce

          then have h7:"SCon (STArray x t) l (Storage st (Address env))" using 2(1) 14
              sameStoLocTSafe sub2
            using SCon_imps_sublocs by blast

          have p:"((if TypedStoSubpref stloc l''' t''' then CompStoType t''' tp'' l''' stloc
               else if TypedStoSubpref l''' stloc tp'' then CompStoType tp'' t''' stloc l''' else True))"
            using 2(1) unfolding TypeSafe_def compPointers_def using sub2 MConsrc by blast

          have denSub:"(if TypedStoSubpref stloc l''' t''' then CompStoType t''' tp'' l''' stloc
             else if TypedStoSubpref l''' stloc tp'' then CompStoType tp'' t''' stloc l''' else True)"
            using p 14(3) by blast
          have paInf:"(tp'' = (STArray x t) \<and> KStoptr p = KStoptr stloc
                  \<or> extractValueType (KStoptr p) \<noteq> stloc \<and> CompStoType tp'' (STArray x t) stloc (extractValueType (KStoptr p)))"
            using MConsrc by simp
          have h8:"SCon (STArray x t) p (Storage st (Address env))" using MConsrc by simp
          have rel:"CompStoType t''' (STArray x t) l''' l" using sub2 14(3) by auto
          have SCondest:"SCon (STArray x t) l s"
            using copy_dest_scon_from_rel[OF 14(4) 14(3) h7 h8 denSub paInf rel] .
          then have SCondest2:"SCon (STArray x t) l (Storage st' (Address env))"
            by (simp add: mInStd)
          then have SCondest3:"SCon t' l (Storage st' (Address env))" using 14(3)
            by (simp add: mInStd )


          have "SCon struct x2 (Storage st' (Address env))"
          proof(cases "TypedStoSubpref l''' x2 struct")
            case True
            then have "CompStoType struct t''' x2 l'''" using cmpStoPtr2 by simp
            then have "CompStoType struct (STArray x t) x2 l" using sub2
              using CompStoType_trns 14(3) by blast
            then show ?thesis using SCondest2 SConx4Old a35 14(3) TypedStoSubpref_shared_parent_related SCon_sub_imps_Parent
              by blast
          next
            case f1:False
            then show ?thesis
            proof(cases "TypedStoSubpref x2 l''' t'''")
              case True
              then have "l''' \<noteq> x2" using f1
                using TypedStoSubpref_sameLoc by auto
              then show ?thesis
              proof(cases "l = x2")
                case t5:True
                then have " CompStoType t''' struct l''' x2" using cmpStoPtr2 f1 14(3) True by simp
                moreover have "CompStoType t''' t' l''' x2" using t5 sub2 by auto
                ultimately have "t' = struct" using CompStoType_sameLocs_sameType
                  by simp
                then show ?thesis using SCondest3 SCon_imps_sublocs t5 by simp
              next
                case False
                then have " CompStoType t''' struct l''' x2" using cmpStoPtr2 f1 14(3) True by simp
                then show ?thesis
                proof(cases "CompStoType t' struct l x2 ")
                  case True
                  then show ?thesis using SCon_imps_sublocs SCondest3 by blast
                next
                  case False
                  then show ?thesis
                    using SCon_imps_sublocs SCon_sub_imps_Parent SCondest2 \<open>CompStoType t''' struct l''' x2\<close> a35 scl''' sub2(2) 14(3) by blast
                qed
              qed
            next
              case False
              then have asm10:"\<not> TypedStoSubpref l x2 struct" using NotRelatedPrnt_imps_notRelatedChild[OF False f1 ] sub2 by blast
              then have asm20:"\<not> TypedStoSubpref x2 l t'" using sub2 NotReachablePrnt_imps_notReachableChild False f1 by blast
              have notSame:"x2 \<noteq> l" using False sub2 by blast
              have k7:"\<forall>locs. TypedStoSubpref locs x2 struct \<longrightarrow> locs \<noteq> l " using f1 sub2 asm10 asm20 by blast
              have k8:"\<forall>locs. TypedStoSubpref locs l (STArray x t) \<longrightarrow> locs \<noteq> x2" using False sub2 14(3) asm10 asm20 by blast
              show ?thesis using sublocs_nonchanged_SCon[OF _ a35 SConx4Old] asm10 asm20 14(3) by blast
            qed
          qed

          then show ?thesis by simp
        next
          case sub3:(3 l''' t''' l'''')
          have cmpStoPtr:"(
              (type.Storage struct, Storeloc x2) |\<in>| fmran (Denvalue env) \<and>
              (type.Storage t''', Stackloc l'''') |\<in>| fmran (Denvalue env) \<and>
               accessStore l'''' (Stack st) = Some (KStoptr l'''))
               \<longrightarrow>
              (if TypedStoSubpref l''' x2 struct then CompStoType struct t''' x2 l'''
               else if TypedStoSubpref x2 l''' t''' then CompStoType t''' struct l''' x2 else True)"
            using 2(1) 14(3) inDen Storeloc structDef unfolding TypeSafe_def compPointers_def by blast

          then have cmpStoPtr2:"(if TypedStoSubpref l''' x2 struct then CompStoType struct t''' x2 l'''
               else if TypedStoSubpref x2 l''' t''' then CompStoType t''' struct l''' x2 else True)"
            using 14(3) sub3 inDen Storeloc structDef 14(3) sameStack by auto

          have SConx4Old:"SCon struct x2 (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using Storeloc inDen 2(1) sameStack structDef
            by fastforce
          have scl''':"SCon t''' l''' (Storage st (Address env))" using 2(1) unfolding TypeSafe_def typeCompat_def using sub3 by fastforce

          then have h7:"SCon (STArray x t) l (Storage st (Address env))" using 2(1) 14
              sameStoLocTSafe sub3
            using SCon_imps_sublocs by blast

          have p:"(
              (if TypedStoSubpref stloc l''' t''' then CompStoType t''' tp'' l''' stloc
               else if TypedStoSubpref l''' stloc tp'' then CompStoType tp'' t''' stloc l''' else True))"
            using 2(1) unfolding TypeSafe_def compPointers_def using sub3 MConsrc by blast

          have denSub:"(if TypedStoSubpref stloc l''' t''' then CompStoType t''' tp'' l''' stloc
             else if TypedStoSubpref l''' stloc tp'' then CompStoType tp'' t''' stloc l''' else True)"
            using p 14(3) by blast
          have paInf:"(tp'' = (STArray x t) \<and> KStoptr p = KStoptr stloc
                  \<or> extractValueType (KStoptr p) \<noteq> stloc \<and> CompStoType tp'' (STArray x t) stloc (extractValueType (KStoptr p)))"
            using MConsrc by simp
          have h8:"SCon (STArray x t) p (Storage st (Address env))" using MConsrc by simp
          have rel:"CompStoType t''' (STArray x t) l''' l" using sub3 14(3) by auto
          have SCondest:"SCon (STArray x t) l s"
            using copy_dest_scon_from_rel[OF 14(4) 14(3) h7 h8 denSub paInf rel] .
          then have SCondest2:"SCon (STArray x t) l (Storage st' (Address env))"
            by (simp add: mInStd)
          then have SCondest3:"SCon t' l (Storage st' (Address env))" using 14(3)
            by (simp add: mInStd )

          have "SCon struct x2 (Storage st' (Address env))"
          proof(cases "TypedStoSubpref l''' x2 struct")
            case True
            then have "CompStoType struct t''' x2 l'''" using cmpStoPtr2 by simp
            then have "CompStoType struct (STArray x t) x2 l" using sub3
              using CompStoType_trns 14(3) by blast
            then show ?thesis using SCondest2 SConx4Old a35 14(3) TypedStoSubpref_shared_parent_related SCon_sub_imps_Parent
              by blast
          next
            case f1:False
            then show ?thesis
            proof(cases "TypedStoSubpref x2 l''' t'''")
              case True
              then have "l''' \<noteq> x2" using f1
                using TypedStoSubpref_sameLoc by auto
              then show ?thesis
              proof(cases "l = x2")
                case t5:True
                then have " CompStoType t''' struct l''' x2" using cmpStoPtr2 f1 14(3) True by simp
                moreover have "CompStoType t''' t' l''' x2" using t5 sub3 by auto
                ultimately have "t' = struct" using CompStoType_sameLocs_sameType
                  by simp
                then show ?thesis using SCondest3 SCon_imps_sublocs t5 by simp
              next
                case False
                then have " CompStoType t''' struct l''' x2" using cmpStoPtr2 f1 14(3) True by simp
                then show ?thesis
                proof(cases "CompStoType t' struct l x2 ")
                  case True
                  then show ?thesis
                    using SCon_imps_sublocs SCondest3 by blast
                next
                  case False
                  then show ?thesis
                    using SCon_imps_sublocs SCon_sub_imps_Parent SCondest2 \<open>CompStoType t''' struct l''' x2\<close> a35 scl''' sub3(3) 14(3) by blast
                qed
              qed
            next
              case False
              then have asm10:"\<not> TypedStoSubpref l x2 struct" using NotRelatedPrnt_imps_notRelatedChild[OF False f1 ] sub3 by blast
              then have asm20:"\<not> TypedStoSubpref x2 l t'" using sub3 NotReachablePrnt_imps_notReachableChild False f1 by blast
              have notSame:"x2 \<noteq> l" using False sub3 by blast
              have k7:"\<forall>locs. TypedStoSubpref locs x2 struct \<longrightarrow> locs \<noteq> l " using f1 sub3 asm10 asm20 by blast
              have k8:"\<forall>locs. TypedStoSubpref locs l (STArray x t) \<longrightarrow> locs \<noteq> x2" using False sub3 14(3) asm10 asm20 by blast
              show ?thesis using sublocs_nonchanged_SCon[OF _ a35 SConx4Old] asm10 asm20 14(3) by blast
            qed
          qed
          then show ?thesis by simp
        qed


        then show ?thesis using Storeloc inDen 2(1) sameStack Storeloc structDef by simp
      qed
    qed
    then have "typeCompat (Denvalue env) (Stack st) (Memory st') (Storage st' (Address env)) cd " using sameStack by simp
  next
    have "Accounts st'= Accounts st" using 14 by auto
    then show "fullyInitialised env (Accounts st') (Stack st')" using 2(3) unfolding fullyInitialised_def
      using sameStack by simp
  next
    have "Stack st = Stack st'" using 14 by simp
    moreover have "Memory st = Memory st'" using 14 by auto
    ultimately show "denvalueTypeCorrectness env (Stack st') (Memory st')"
      using 2(1) unfolding TypeSafe_def by simp
  next
    show "subPrefixStructuralConsistency (Memory st')"
      using 2(1) 14 unfolding TypeSafe_def by simp
  next
    show " SomeValSomeTyp (Memory st') " using 2(1) unfolding TypeSafe_def using 14 by simp
  next
    show "\<And>locs t. accessTypeStore locs (Memory st) = Some t \<Longrightarrow> accessTypeStore locs (Memory st') = Some t"
      using 2(1) 14 unfolding TypeSafe_def by simp
  next
    show "\<And>locs v. accessStore locs (Memory st) = Some (MPointer v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MPointer v')"
      using 14 by auto
  next
    show "\<And>locs v. accessStore locs (Memory st) = Some (MValue v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MValue v')"
      using 14 by auto
  next
    show " \<And>i loc. i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<Longrightarrow> accessStore loc
        (Memory st) = None \<Longrightarrow> accessStore loc (Memory st') = None"
      using 14 by auto
  next
    show "Toploc (Memory st) \<le> Toploc (Memory st')" using 14 by auto
  qed
qed

text \<open>Assignment case 15: a storage array assigned to a memory location: the array is copied into fresh memory and the location is updated to point to it.\<close>

lemma TypeSafe_Assign_15:
  assumes "TypeSafe env (Accounts st) (Stack st) (Memory st) (Storage st) cd"
    and "stmt (ASSIGN lv ex) env cd st = Normal ((), st')"
    and "fullyInitialised env (Accounts st) (Stack st)"
    and "expr ex env cd (st\<lparr>state.Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>) (state.Gas st - costs (ASSIGN lv
        ex) env cd st) = Normal ((KStoptr p, type.Storage (STArray x t)), g)"
    and "lexp lv env cd (st\<lparr>state.Gas := g\<rparr>) g = Normal((LMemloc l, type.Memory t'),g')"
    and "cps2mTypeCompatible (STArray x t) t'"
    and "cps2m p (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) x t (Storage st (Address env)) (snd (allocate(Memory st))) = Some m"
    and "updateStore l (MPointer ((ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))))) m = m'"
    and "st' = st\<lparr>state.Gas := g', Memory := m'\<rparr>"
  shows "StateInvariant env st st' cd"
proof -
  let ?case = "StateInvariant env st st' cd"
  note 2 = assms(1-3)
  note 15 = assms(4-9)
  have temp:"TypeSafe env (Accounts (st\<lparr>Gas := g\<rparr>)) (Stack (st\<lparr>Gas := g\<rparr>)) (Memory (st\<lparr>Gas := g\<rparr>)) (Storage (st\<lparr>Gas := g\<rparr>)) cd"
    using 2(1) by simp
  have ttt:"fullyInitialised env (Accounts (st\<lparr>Gas := g\<rparr>)) (Stack (st\<lparr>Gas := g\<rparr>))" using 2(3) unfolding fullyInitialised_def by simp

  then show ?thesis
  proof(cases rule:lexpIndexMem[OF 15(2) temp ttt])
    case lInfo:(1 x21 x22 tp tParent l' l'' prnt len' arr' i)
    have nonChangedStack:"\<forall>loc. loc \<noteq> l \<longrightarrow> accessStore loc (Stack st) = accessStore loc (Stack st')" using 15 unfolding accessStore_def updateStore_def by auto
    have sameStack:"(Stack st') = Stack st" using 15 unfolding accessStore_def updateStore_def by auto
    have sameStorage:"Storage st' = Storage st " using 15 by auto
    have nonLocChanged:"\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<or> locs =
        (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))\<longrightarrow> accessStore locs (snd (allocate (Memory st))) = accessStore
        locs m"
      using 15(4) unfolding cps2m_def using cps2mSingleChange[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t "(Storage st
          (Address env))" " (snd (allocate (Memory st)))" x m ] cps2m_def[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" x
          t "(Storage st (Address env))" " (snd (allocate (Memory st)))" ]
      by fastforce
    have a30:"\<forall>locs. locs \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> \<not> TypedStoSubpref locs
        (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (STArray x t) \<longrightarrow> accessStore locs (snd (allocate (Memory st)))
        = accessStore locs m"
      using 15(4) unfolding cps2m_def using cps2mSingleChange_typedPref[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t "(Storage
          st (Address env))" " (snd (allocate (Memory st)))" x m ] by fastforce
    then have a32:"\<forall>locs. \<not> TypedStoSubpref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (STArray x t) \<longrightarrow> accessStore locs (Memory st) = accessStore locs m"
      by (metis allocateSameAccess nonLocChanged)
    have selfPoint:"\<forall>l l'. l \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> TypedStoSubpref l
        (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (STArray x t) \<and> accessStore l m = Some (MPointer l') \<longrightarrow>
        l' = l"
      using 15(4) unfolding cps2m_def
      using cps2mSelfPointers[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t "(Storage st (Address env))" " (snd (allocate (Memory st)))" x m ]
      by blast
    have mInStd:"m' = Memory st'" using 15 by simp
    have NonChangeM'm:"\<forall>locs. locs \<noteq> l \<longrightarrow> accessStore locs m = accessStore locs m'" using 15(5) unfolding accessStore_def updateStore_def by auto
    have accessL:"accessStore l m' = Some (MPointer (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))))" using 15(5) unfolding accessStore_def updateStore_def by auto

    have MConsrc:"SCon (STArray x t) (extractValueType (KStoptr p)) (Storage (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd
        st\<rparr>) (Address env)) \<and> (\<exists>xx. KStoptr p = KStoptr xx)"
      using 2(1) 15(1) exprTypeconInduct(3)[of ex env cd "(st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)"
          "(state.Gas st - costs (ASSIGN lv ex) env cd st)" ] 2(3)unfolding fullyInitialised_def
      by (auto split:type.splits if_splits )

    obtain memArr where memArrDef: "t' = MTArray x memArr" using 15(3) cps2mTypeCompatible.simps
      by (metis mtypes.exhaust)

    have limitSt1:"(\<forall>loc y. accessStore loc (Memory st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Memory st). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))"
      using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by simp
    have limitSt:"(\<forall>tloc loc. Toploc (Memory st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Memory st) = None)"
      using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by simp
    moreover have allocateSame:"\<forall>loc. accessStore loc (Memory st) = accessStore loc (snd (allocate (Memory st)))"
      using allocateSameAccess by blast
    ultimately have "accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (snd (allocate (Memory st))) = None" using LSubPrefL2_def by auto
    then have MCondest:" MCon (MTArray x memArr) m (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" using 15(4,3) unfolding cps2m_def
      using cps2m[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t "(Storage st (Address env))" "(snd (allocate (Memory st)))" x m memArr]
        MConsrc extractValueType.simps(2) memArrDef by auto
    have "\<exists>x. accessStore l (Memory st) = Some x" using lInfo by (auto split:option.splits)
    then have l_not_toploc_orSub:"\<not>LSubPrefL2 l (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))"
      using limitSt by fastforce

    have selfPoint2:"\<forall>l1 l2. LSubPrefL2 l1 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))
                      \<and> accessStore l1 (Memory st') = Some (MPointer l2) \<longrightarrow> l2 = l1 \<and> l1 \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))"
      by (metis (no_types, lifting) "15"(4) NonChangeM'm
          \<open>accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (state.Memory st))) (snd (allocate (state.Memory st))) = None\<close> a32 cps2mSelfPointers cps2m_def
          dual_order.refl l_not_toploc_orSub limitSt mInStd nonLocChanged option.discI)


    obtain len subT where tParentType:"tParent = MTArray len subT" using lInfo by blast
    then obtain p'' where lOrigin:"accessStore l (Memory (st)) = Some (MPointer p'')"
        and compType:"CompMemType (Memory (st\<lparr>Gas := g\<rparr>)) len subT (MTArray x memArr) l'' p''"
        and lsublocs:"l = hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<and> i < len' \<and> arr' = (MTArray x memArr) \<and> MCon (MTArray len' arr') (Memory (st)) prnt"
        and lsublocs3:"(prnt = l'' \<and> len = len' \<and> arr' = subT \<or> CompMemType (Memory (st)) len subT (MTArray len' arr') l'' prnt)"
      using lInfo 15(3) memArrDef by force
    then have lsublocs2:" CompMemType (Memory (st)) len' arr' (MTArray x memArr) prnt p''"
      using "15"(3) CompMemType.simps(2) memArrDef by blast

    then have bb9:"\<forall>subT subloc. CompMemType (Memory (st)) len' arr' subT prnt subloc \<and> subloc = p''
                                \<longrightarrow> subT = (MTArray x memArr)"
      using CompMemTypeSameLocsSameType lsublocs by blast

    have mconPrnt:"MCon (MTArray len' (MTArray x memArr)) (Memory st) prnt" using lsublocs by auto
    have ldef:"l = hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<and> i < len'" using lsublocs by auto

    have t6:"(type.Memory tParent, Stackloc l') |\<in>| fmran (Denvalue env)" using lInfo by blast
    have t7:" MCon (MTArray len subT) (Memory (st)) l''" using lInfo
      using tParentType by auto
    then have t8:"\<not> LSubPrefL2 l'' (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" using limitSt limitSt1 typeSafe_noDenElementOverToploc_mem[OF 2(1) t6] lInfo(3) by simp
    have comptype2:"CompMemType m len subT (MTArray x memArr) l'' p''" using
        cpm2mCompMemTypeOld_imps_CompMemType[of "(Memory (st\<lparr>Gas := g\<rparr>))" len subT "(MTArray x memArr)" l'' p'' "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" m ]
        compType nonLocChanged limitSt t7 t8 allocateSame by auto
    have t10:"CompMemType (Memory st) len subT (MTArray x memArr) l'' p''"
      using
        cpm2mCompMemTypeOld_imps_CompMemType[of "(Memory (st\<lparr>Gas := g\<rparr>))" len subT "(MTArray x memArr)" l'' p'' "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" m ]
        compType nonLocChanged limitSt t7 t8 allocateSame by auto
    then have mconlOld:"MCon (MTArray x memArr) (Memory st) p''" using memArrDef 15(3) lInfo lOrigin by auto

    have nonLocChanged2:"\<forall>locs. locs \<noteq> l \<and> \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))
        \<longrightarrow> accessStore locs (Memory st) = accessStore locs (Memory st')"
      using 15 nonLocChanged LSubPrefL2_def NonChangeM'm mInStd allocateSame by metis
    have stackDenvalLimits:"\<forall>struct loc stloc. (type.Memory struct, Stackloc loc) |\<in>| fmran (Denvalue env)
                        \<and> accessStore loc (Stack st) = Some (KMemptr stloc) \<longrightarrow> \<not> LSubPrefL2 stloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))"
      using typeSafe_noDenElementOverToploc_mem[OF 2(1)] by auto
    have selfPoint_root:"\<forall>l1 l2. TypedStoSubpref l1 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (STArray x t) \<and> accessStore l1 m = Some (MPointer l2) \<longrightarrow> l2 = l1"
    proof (intro allI impI)
      fix l1 l2
      assume asm:"TypedStoSubpref l1 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (STArray x t) \<and> accessStore l1 m = Some (MPointer l2)"
      have l1_neq:"l1 \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))"
        using asm TypedStoSubpref_imp_LSubPrefL2 hash_inequality
        using \<open>accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (state.Memory st))) (snd (allocate (state.Memory st))) = None\<close> nonLocChanged
        by fastforce
      then show "l2 = l1"
        using selfPoint asm by blast
    qed
    have MCondest2:" MCon (MTArray x memArr) (Memory st') (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) " using 15 MCondest memArrDef
    proof -
      have "\<not> LSubPrefL2 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) l"
        using l_not_toploc_orSub MemLSubPrefTransitive LSubPrefL2_refl by blast
      moreover have "\<forall>d. \<not> LSubPrefL2 d l \<longrightarrow> accessStore d m = accessStore d (Memory st')"
        using NonChangeM'm mInStd LSubPrefL2_refl by metis
      moreover have "cps2mTypeCompatible (STArray x t) (MTArray x memArr)"
        using 15(3) memArrDef by simp
      ultimately show ?thesis
        using MCon_preserved_under_disjoint_location[of "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" l "STArray x t" m
            "MTArray x memArr" "Memory st'"] selfPoint_root l_not_toploc_orSub MCondest by blast
    qed

    have bb:"\<forall>locs tp. CompMemType (Memory st) len subT tp l'' locs \<longrightarrow> locs \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t
        (Toploc (Memory st))) \<and> \<not>LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))"
    proof intros
      fix locs tp
      assume asm1:"CompMemType (Memory st) len subT tp l'' locs"
      then have a2:"locs \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" using t7
      proof(induction subT arbitrary:len l'')
        case (MTArray x1 subT)
        then show ?case
          using CompMemType_imps_TypedMemSubPrefPtrs LSubPrefL2_def limitSt limitSt1 subPtrs_nonTop by blast
      next
        case (MTValue x)
        then show ?case
          by (metis (no_types, lifting) CompMemType_imps_TypedMemSubPrefPtrs LSubPrefL2_def limitSt limitSt1 subPtrs_nonTop)
      qed
      then show " locs \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" by simp
      show "\<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) " using a2 by simp
    qed
    have b8:"\<forall>locs tp. CompMemType m len subT tp l'' locs \<longrightarrow> locs \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))"
    proof intros
      fix locs tp
      assume asm1:"CompMemType m len subT tp l'' locs"
      then show "locs \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" using t7 bb a32
      proof(induction subT arbitrary:len l'')
        case (MTArray x1 subT)
        obtain i' ptr' where i'Def:"i'<len \<and> accessStore (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i')) m = Some (MPointer ptr')
            \<and> (ptr' = locs \<and> MTArray x1 subT = tp \<or> CompMemType m x1 subT tp ptr' locs)"
          using MTArray.prems(1) unfolding CompMemType.simps by blast
        have "\<not> TypedMemSubPref (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x memArr)"

          by (metis MTArray.prems(2) bot_nat_0.extremum_unique i'Def leI limitSt mcon_accessStore nat_less_le neg_MemLSubPrefL2_imps_TypedMemSubPref not_Some_eq)
        then have "accessStore (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (Memory st) = accessStore (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i')) m" using MTArray.prems memArrDef
          by (metis MConArrayPointers allocateSame bot_nat_0.extremum_strict bot_nat_0.not_eq_extremum i'Def le_refl limitSt nonLocChanged option.distinct(1))
        then show ?case
        proof(cases "ptr' = locs")
          case True
          then show ?thesis
            using MTArray.prems(3) \<open>accessStore (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (Memory st) = accessStore (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i')) m\<close> i'Def by auto
        next
          case False
          then have "CompMemType m x1 subT tp ptr' locs"
            using i'Def by blast
          moreover have "MCon (MTArray x1 subT) (Memory st) ptr'"
            by (metis MCon_imps_sub_Mcon MTArray.prems(2) \<open>accessStore (hash
                l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (Memory st) = accessStore (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i')) m\<close>
                i'Def)
          moreover have "\<forall>locs tp. CompMemType (Memory st) x1 subT tp ptr' locs \<longrightarrow> locs \<noteq>
              (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc
              (Memory st)))"
            using MTArray.prems(3)
            by (metis (no_types, lifting) CompTypeRemainsMCon MCon_imps_Some LSubPrefL2_def \<open>MCon (MTArray x1 subT) (Memory st)
                ptr'\<close> Not_Sub_More_Specific le_refl limitSt option.distinct(1))
          ultimately show ?thesis using MTArray.IH[of x1 ptr'] using MTArray.prems by blast
        qed
      next
        case (MTValue x)
        then show ?case by simp
      qed
    qed

    have nonLocChanged22:" \<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<or> locs =
        (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow> accessStore locs (Memory st) = accessStore locs m" using
        nonLocChanged
      by (simp add: allocateSame)
    then have l''mMcon:" MCon (MTArray len subT) m l''" using t7 bb
    proof(induction subT arbitrary: len l'')
      case (MTArray x1 subT)
      have "\<forall>i<len.
           (case accessStore (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m of None \<Rightarrow> False
            | Some (MValue val) \<Rightarrow> (case MTArray x1 subT of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon
                (MTArray x1 subT) m (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
            | Some (MPointer loc2) \<Rightarrow> (case MTArray x1 subT of MTArray len' arr' \<Rightarrow> MCon (MTArray x1 subT) m loc2 | MTValue Types \<Rightarrow> False))"
      proof(intros)
        fix i assume asm1:"i<len"
        then obtain ptr' where ptr'def:"accessStore (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some (MPointer ptr')
                        \<and> MCon (MTArray x1 subT) (Memory st) ptr'" using MTArray(3)
          by (metis MConArrayPointers MCon_imps_sub_Mcon MCon.simps(2))
        have "CompMemType (Memory st) len (MTArray x1 subT) (MTArray x1 subT) l'' (ptr')"
          using ptr'def asm1 by auto
        then have "ptr' \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> \<not> LSubPrefL2 ptr' (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))"
          using MTArray.prems(3) by blast
        have same:"accessStore (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = accessStore (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (m)" using nonLocChanged22
          by (metis Read_Show_nat'_id antisym_conv1 limitSt option.distinct(1) ptr'def readLintNotEqual)

        have "\<forall>locs tp. CompMemType (Memory st) x1 subT tp ptr' locs \<longrightarrow> locs \<noteq>
            (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc
            (Memory st)))"
          using MTArray.prems(3) \<open>CompMemType (Memory st) len (MTArray x1 subT) (MTArray x1 subT) l'' ptr'\<close> compMemTypes_trns by blast
        then have "MCon (MTArray x1 subT) m ptr'" using MTArray.IH[of x1 ptr'] ptr'def
          using nonLocChanged22 by blast
        then show "(case accessStore (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m of None \<Rightarrow> False
            | Some (MValue val) \<Rightarrow> (case MTArray x1 subT of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon
                (MTArray x1 subT) m (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
            | Some (MPointer loc2) \<Rightarrow> (case MTArray x1 subT of MTArray len' arr' \<Rightarrow> MCon (MTArray x1 subT) m loc2 | MTValue Types \<Rightarrow> False))" using same ptr'def
          by (metis mtypes.simps(5) memoryvalue.simps(6) Option.option.simps(5))
      qed
      moreover have "len > 0" using MTArray.prems unfolding MCon.simps by blast
      moreover have "(\<exists>p. accessStore l'' m = Some (MPointer p)) \<or> accessStore l'' m = None"
      proof(cases "l'' = l")
        case True
        then show ?thesis
          using lOrigin l_not_toploc_orSub nonLocChanged22 by auto
      next
        case False
        then have "accessStore (l'' ) (Memory st) = accessStore (l'') (m)" using nonLocChanged22
          by (metis MConArrayPointers MTArray.prems(2) Read_Show_nat'_id calculation(2) lessThanSome_imps_Locs_hash lessThanTopLocs_def limitSt limitSt1 readLintNotEqual)
        then show ?thesis
          using MTArray.prems(2) calculation(2) by force
      qed
      ultimately show ?case using MCon.simps(2)[of len "MTArray x1 subT" m l'']
        by simp
    next
      case (MTValue x)
      have "\<forall>i<len.
           (case accessStore (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m of None \<Rightarrow> False
| Some (MValue val) \<Rightarrow> (case MTValue x of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTValue x) m (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
            | Some (MPointer loc2) \<Rightarrow> (case MTValue x of MTArray len' arr' \<Rightarrow> MCon (MTValue x) m loc2 | MTValue Types \<Rightarrow> False))"
      proof(intros)
        fix i assume asm1:"i<len"
        then obtain val where ptr':"accessStore (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some (MValue val)
                        \<and> MCon (MTValue x) (Memory st) (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using MTValue(2)
          by (metis MCon_imps_sub_Mcon MCon_sub_MTVal_imps_val)
        then have " CompMemType (Memory st) len (MTValue x) (MTValue x) l'' (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using asm1 by auto
        then have "(hash
            l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> \<not> LSubPrefL2
                (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))"
          using MTValue by blast
        then have "accessStore (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = accessStore (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (m)" using nonLocChanged22 by auto
        then show "(case accessStore (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m of None \<Rightarrow> False | Some (MValue val) \<Rightarrow>
(case MTValue x of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTValue x) m (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
            | Some (MPointer loc2) \<Rightarrow> (case MTValue x of MTArray len' arr' \<Rightarrow> MCon (MTValue x) m loc2 | MTValue Types \<Rightarrow> False))"
          using ptr' asm1
          by (metis mtypes.simps(6) memoryvalue.simps(5) Option.option.simps(5) MCon.simps(1))
      qed
      moreover have "(\<exists>p. accessStore l'' m = Some (MPointer p)) \<or> accessStore l'' m = None"
      proof(cases "l'' =l")
        case True
        then show ?thesis
          using lOrigin l_not_toploc_orSub nonLocChanged22 by auto
      next
        case False
        then have "accessStore (l'' ) (Memory st) = accessStore (l'') (m)" using nonLocChanged22
          by (metis MCon_imps_Some MTValue.prems(2) Read_Show_nat'_id antisym_conv1 lessThanSome_imps_Locs_hash lessThanTopLocs_def limitSt limitSt1 option.discI readLintNotEqual)

        then show ?thesis
          by (metis MTValue.prems(2) MCon.simps(2))
      qed
      moreover have "len > 0" using MTValue by fastforce
      ultimately show ?case using MCon.simps(2)[of len "MTValue x" m l''] by simp
    qed

    have p''mMcon:"MCon (MTArray x memArr) m p''" using mconlOld
    proof(induction memArr arbitrary:x p'')
      case (MTArray x1 t)
      have samep'':"p'' \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> \<not>LSubPrefL2 p'' (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))"
        by (metis (no_types, lifting) MCon_imps_Some MTArray(2) LSubPrefL2_def Not_Sub_More_Specific le_refl limitSt option.distinct(1))
      have "x > 0" using MTArray
        using zero_less_iff_neq_zero by force
      moreover have "(\<exists>p. accessStore p'' m = Some (MPointer p)) \<or> accessStore p'' m = None" using MTArray samep''
        using nonLocChanged22 calculation(1) by force
      moreover have "\<forall>i<x. (case accessStore (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m of None \<Rightarrow> False
                | Some (MValue val) \<Rightarrow> (case MTArray x1 t of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon
                    (MTArray x1 t) m (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
               | Some (MPointer loc2) \<Rightarrow> (case MTArray x1 t of MTArray len' arr' \<Rightarrow> MCon (MTArray x1 t) m loc2 | MTValue Types \<Rightarrow> False))"
      proof(intros)
        fix i assume asm1:"i<x"
        then obtain ptr where ptr':"accessStore (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some (MPointer ptr) \<and> MCon (MTArray x1 t) (Memory st) ptr" using MTArray
          by (meson MConArrayPointers MCon_imps_sub_Mcon \<open>0 < x\<close>)
        moreover have "accessStore (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = accessStore (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st)"
          using MemLSubPrefL2_specific_imps_general
              \<open>p'' \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> \<not> LSubPrefL2 p''
              (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))\<close> nonLocChanged22 by metis
        moreover have "accessStore ptr (Memory st) = accessStore ptr (m)"
          using nonLocChanged22
          by (metis MCon_imps_Some Read_Show_nat'_id antisym_conv1 calculation(1) lessThanSome_imps_Locs_hash lessThanTopLocs_def limitSt limitSt1 option.discI readLintNotEqual)
        moreover have "MCon (MTArray x1 t) m ptr" using MTArray.IH ptr' by blast
        ultimately show "case accessStore (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m of None \<Rightarrow> False
      | Some (MValue val) \<Rightarrow> (case MTArray x1 t of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTArray x1 t) m (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
       | Some (MPointer loc2) \<Rightarrow> (case MTArray x1 t of MTArray len' arr' \<Rightarrow> MCon (MTArray x1 t) m loc2 | MTValue Types \<Rightarrow> False)" by simp
      qed
      ultimately show ?case using MCon.simps(2)[of x "MTArray x1 t" m p''] by simp
    next
      case (MTValue x')
      have "p'' \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> \<not>LSubPrefL2 p'' (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))"
        by (metis (no_types, lifting) MCon_imps_Some MTValue LSubPrefL2_def Not_Sub_More_Specific le_refl limitSt option.distinct(1))
      then have samep':"accessStore p'' (Memory st) = accessStore p'' m"
        by (simp add: nonLocChanged22)
      have "\<forall>i<x. (case accessStore (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m of None \<Rightarrow> False
| Some (MValue val) \<Rightarrow> (case MTValue x' of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTValue x') m (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
               | Some (MPointer loc2) \<Rightarrow> (case MTValue x' of MTArray len' arr' \<Rightarrow> MCon (MTValue x') m loc2 | MTValue Types \<Rightarrow> False))"
      proof(intros)
        fix i assume asm1:"i<x"
        then obtain val where "accessStore (hash
            p'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some (MValue val) \<and> MCon (MTValue x') (Memory st) (hash p''
            (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using MTValue
          by (meson MCon_imps_sub_Mcon MCon_sub_MTVal_imps_val)
        moreover have "accessStore (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = accessStore (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (m)"
          using MemLSubPrefL2_specific_imps_general
              \<open>p'' \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> \<not> LSubPrefL2 p''
              (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))\<close> nonLocChanged22 by blast
        ultimately show "(case accessStore (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m of None \<Rightarrow> False
                | Some (MValue val) \<Rightarrow> (case MTValue x' of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTValue x') m (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
               | Some (MPointer loc2) \<Rightarrow> (case MTValue x' of MTArray len' arr' \<Rightarrow> MCon (MTValue x') m loc2 | MTValue Types \<Rightarrow> False))"
          by auto
      qed
      moreover have "x > 0" using MTValue
        using zero_less_iff_neq_zero by force
      moreover have "(\<exists>p. accessStore p'' m = Some (MPointer p)) \<or> accessStore p'' m = None" using MTValue samep'
        using calculation(2) by auto
      ultimately show ?case using MCon.simps(2)[of x "MTValue x'" m p''] by simp
    qed

    have prntMconNew:"MCon (MTArray len' (MTArray x memArr)) (Memory st') prnt"
    proof -
      have " \<forall>i<len'.
           (case accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') of None \<Rightarrow> False
            | Some (MValue val) \<Rightarrow> (case MTArray x memArr of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon
                (MTArray x memArr) (Memory st') (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
            | Some (MPointer loc2) \<Rightarrow> (case MTArray x memArr of MTArray len' arr' \<Rightarrow> MCon (MTArray x memArr) (Memory st') loc2 | MTValue Types \<Rightarrow> False))"
      proof intros
        fix i' assume asm1:"i'<len'"
        then obtain ptr where ptrDef': "accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (Memory st) = Some(MPointer ptr)
                                " and ptrDef'2:"MCon (MTArray x memArr) (Memory st) ptr"
          using mconPrnt by (metis MConArrayPointers MCon_imps_sub_Mcon bot_nat_0.not_eq_extremum not_less_zero)

        show "case accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (Memory st') of None \<Rightarrow> False
            | Some (MValue val) \<Rightarrow> (case MTArray x memArr of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon
                (MTArray x memArr) (Memory st') (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i')))
            | Some (MPointer loc2) \<Rightarrow> (case MTArray x memArr of MTArray len' arr' \<Rightarrow> MCon (MTArray x memArr) (Memory st') loc2 | MTValue Types \<Rightarrow> False)"
        proof(cases "i' = i")
          case True
          then show ?thesis
            using MCondest2 accessL ldef mInStd by force
        next
          case False
          then have "accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (Memory st) = accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (Memory st')" using ldef
            by (metis hashesIntSame limitSt nle_le nonLocChanged2 option.distinct(1) ptrDef')
          then have same:"accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (Memory st') = Some(MPointer ptr)" using ptrDef' by simp

          have locRule:"\<forall>ct locs ints. CompMemType (Memory st) len' (MTArray x memArr) ct prnt locs \<longrightarrow> locs
              \<noteq> prnt \<and> hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t ints) \<noteq> l"
            using BothMConImpsNotCompMemType CompTypeRemainsMCon mconPrnt ldef ShowLNatDot hash_injective by metis
          have "CompMemType (Memory st) len' (MTArray x memArr) (MTArray x memArr) prnt ptr" using ptrDef' asm1 by auto
          then have "MCon (MTArray x memArr) (Memory st') ptr" using ptrDef'2 locRule
          proof(induction memArr arbitrary: x ptr len' prnt)
            case (MTArray x11 x12)
            have "\<forall>i<x. (case accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') of None \<Rightarrow> False
             | Some (MValue val) \<Rightarrow> (case MTArray x11 x12 of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon
                 (MTArray x11 x12) (Memory st') (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
             | Some (MPointer loc2) \<Rightarrow> (case MTArray x11 x12 of MTArray len' arr' \<Rightarrow> MCon (MTArray x11 x12) (Memory st') loc2 | MTValue Types \<Rightarrow> False))"
            proof intros
              fix i'' assume "i''<x"
              then obtain ptr' where ptr'Def:"accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st) = Some(MPointer ptr')
                                              \<and> MCon (MTArray x11 x12) (Memory st) ptr'" using MTArray.prems(2)
                by (metis MConArrayPointers MCon_imps_sub_Mcon neq0_conv not_less_zero)
              have "ptr \<noteq> prnt" using MTArray.prems by blast
              then have "(hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) \<noteq> l" using MTArray.prems ShowLNatDot hash_injective by blast
              then have "accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st) = accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st')"
                by (metis less_or_eq_imp_le limitSt nonLocChanged2 option.discI ptr'Def)
              then have same2:"accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st') = Some(MPointer ptr')" using ptr'Def by simp

              have "MCon (MTArray x11 x12) (Memory st) ptr'" using ptr'Def by blast
              moreover have "CompMemType (Memory st) x (MTArray x11 x12) (MTArray x11 x12) ptr ptr'" using ptr'Def
                using \<open>i'' < x\<close> by auto
              moreover have "\<forall>ct locs ints. CompMemType (Memory st) x (MTArray x11 x12) ct ptr locs \<longrightarrow> locs
                  \<noteq> ptr \<and> hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t ints) \<noteq> l"
                by (metis BothMConImpsNotCompMemType CompTypeRemainsMCon MTArray.prems(1,2,3) compMemTypes_trns)
              ultimately have "MCon (MTArray x11 x12) (Memory st') ptr'" using MTArray.IH[of x x11 ptr ptr'] by blast
              then show "(case accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st') of None \<Rightarrow> False
             | Some (MValue val) \<Rightarrow> (case MTArray x11 x12 of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon
                 (MTArray x11 x12) (Memory st') (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i'')))
             | Some (MPointer loc2) \<Rightarrow> (case MTArray x11 x12 of MTArray len' arr' \<Rightarrow> MCon (MTArray x11 x12) (Memory st') loc2 | MTValue Types \<Rightarrow> False))"
                using ptrDef' same2 by auto
            qed

            moreover have xNotZero:"x>0" using MTArray.prems(2)
              using bot_nat_0.not_eq_extremum by fastforce
            moreover have "(\<exists>p. accessStore ptr (Memory st') = Some (MPointer p)) \<or> accessStore ptr (Memory st') = None"
            proof(cases "ptr = l")
              case True
              then have " accessStore ptr (Memory st') = Some (MPointer (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))))" using 15 by auto
              then show ?thesis by blast
            next
              case False
              then have pdef:"(\<exists>p. accessStore ptr (Memory st) = Some (MPointer p)) \<or> accessStore ptr (Memory st) = None"
                using MTArray.prems(2) MCon.simps(2)[of x _ "Memory st" ptr] xNotZero by simp
              then have "\<not> LSubPrefL2 ptr (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" using limitSt1 limitSt
                by (metis (no_types, lifting) MCon_imps_Some MTArray.prems(2) LSubPrefL2_def Not_Sub_More_Specific le_refl option.distinct(1))
              then have "accessStore ptr (Memory st) =accessStore ptr (Memory st') " using False nonLocChanged2 by simp
              then show ?thesis using pdef by simp
            qed
            ultimately show ?case using MCon.simps(2)[of x "MTArray x11 x12" "Memory st'" ptr] by simp
          next
            case (MTValue x2)
            have "\<forall>i<x. (case accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') of None \<Rightarrow> False
               | Some (MValue val) \<Rightarrow> (case MTValue x2 of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon
                   (MTValue x2) (Memory st') (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
               | Some (MPointer loc2) \<Rightarrow> (case MTValue x2 of MTArray len' arr' \<Rightarrow> MCon (MTValue x2) (Memory st') loc2 | MTValue Types \<Rightarrow> False))"
            proof intros
              fix i'' assume "i''<x"
              then obtain val where oldDef:"accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st) = Some(MValue val)
                                              \<and> MCon (MTValue x2) (Memory st) (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i''))" using MTValue ptrDef'
                by (meson MCon_imps_sub_Mcon MCon_sub_MTVal_imps_val)
              have "(hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) \<noteq> l " using MTValue ldef ShowLNatDot hash_injective by blast
              then have "accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st) = accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st')"
                by (metis less_or_eq_imp_le limitSt nonLocChanged2 option.discI oldDef)
              then have "accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st') = Some(MValue val)" using oldDef by simp
              then show "case accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st') of None \<Rightarrow> False
                     | Some (MValue val) \<Rightarrow> (case MTValue x2 of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow>
                         MCon (MTValue x2) (Memory st') (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i'')))
                     | Some (MPointer loc2) \<Rightarrow> (case MTValue x2 of MTArray len' arr' \<Rightarrow> MCon (MTValue x2) (Memory st') loc2 | MTValue Types \<Rightarrow> False)"
                using oldDef by auto
            qed
            moreover have xNotZero:"x>0" using MTValue(2)
              using bot_nat_0.not_eq_extremum by fastforce
            moreover have "(\<exists>p. accessStore ptr (Memory st') = Some (MPointer p)) \<or> accessStore ptr (Memory st') = None"
            proof(cases "ptr = l")
              case True
              then have " accessStore ptr (Memory st') = Some (MPointer (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))))" using 15 by auto
              then show ?thesis by blast
            next
              case False
              then have pdef:"(\<exists>p. accessStore ptr (Memory st) = Some (MPointer p)) \<or> accessStore ptr (Memory st) = None"
                using MTValue(2) MCon.simps(2)[of x _ "Memory st" ptr] xNotZero by simp
              then have "\<not> LSubPrefL2 ptr (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" using limitSt1 limitSt
                by (metis (no_types, lifting) MCon_imps_Some MTValue(2) LSubPrefL2_def Not_Sub_More_Specific le_refl option.distinct(1))
              then have "accessStore ptr (Memory st) =accessStore ptr (Memory st') " using False nonLocChanged2 by simp
              then show ?thesis using pdef by simp
            qed

            ultimately show ?case using MCon.simps(2)[of x "MTValue x2" "Memory st'" ptr] by simp
          qed
          then show ?thesis using same asm1 by simp
        qed
      qed

      moreover have "len' > 0" using mconPrnt
        using ldef by auto
      moreover have "prnt \<noteq> l" using ldef
        by (metis hash_inequality)
      moreover have "(\<exists>p. accessStore prnt (Memory st') = Some (MPointer p)) \<or> accessStore prnt (Memory st') = None"
      proof(cases "LSubPrefL2 prnt (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))")
        case True
        then show ?thesis
          by (metis LSubPrefL2_def Not_Sub_More_Specific l_not_toploc_orSub ldef)
      next
        case False
        then show ?thesis using nonLocChanged2 calculation mconPrnt by simp
      qed
      ultimately show ?thesis using MCon.simps(2)[of len' "MTArray x memArr" "Memory st'" prnt] mconPrnt nonLocChanged2 ldef by simp
    qed

    have compmemst':"\<forall>locs lens subTs. CompMemType (Memory st) lens subTs (MTArray len' arr') locs prnt
                          \<and> MCon (MTArray lens subTs) (Memory st) locs
                        \<longrightarrow> CompMemType (Memory (st')) lens subTs (MTArray len' arr') locs prnt \<and> CompMemType (m) lens subTs (MTArray len' arr') locs prnt"
    proof intros
      fix locs lens subTs
      assume asm1:"CompMemType (Memory st) lens subTs (MTArray len' arr') locs prnt \<and> MCon (MTArray lens subTs) (Memory st) locs"
      then have asm5:"CompMemType (Memory st) lens subTs (MTArray len' arr') locs prnt" by blast
      have asm6:"MCon (MTArray lens subTs) (Memory st) locs" using asm1 by blast
      have asm2:"\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow> accessStore locs (Memory (st)) = accessStore locs m"
        using nonLocChanged allocateSame by auto
      have mconl'':"MCon (MTArray len subT) (Memory st) l''" using lInfo(5) tParentType by simp

      have a5:"CompMemType m lens subTs (MTArray len' arr') locs prnt" using cpm2mCompMemTypeOld_imps_CompMemType[OF asm5 asm2 ] asm6 limitSt
        by (metis (no_types, opaque_lifting) MCon_imps_Some LSubPrefL2_def eq_imp_le Not_Sub_More_Specific not_None_eq)
      then have a10:"CompMemType (Memory st') lens subTs (MTArray len' arr') locs prnt \<and> CompMemType m lens subTs (MTArray len' arr') locs prnt" using asm6
      proof(induction subTs arbitrary: lens locs)
        case (MTArray x11 x12)
        then have "CompMemType m lens (MTArray x11 x12) (MTArray len' arr') locs prnt" using a5 by simp
        then obtain iIn lIn where iInDef:"iIn<lens \<and> accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t iIn)) m = Some (MPointer lIn)
                  \<and> (lIn = prnt \<and> MTArray x11 x12 = MTArray len' arr' \<or> CompMemType m x11 x12 (MTArray len' arr') lIn prnt)"
          unfolding CompMemType.simps by blast
        have same2:" accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t iIn)) m = accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t iIn)) (Memory st)"
          using MConArrayPointers MTArray.prems(2) allocateSame bot_nat_0.not_eq_extremum iInDef le_eq_less_or_eq limitSt nonLocChanged not_less_zero option.discI by metis
        then have mcIn:"MCon (MTArray x11 x12) (Memory st) lIn" using same2 iInDef MTArray.prems
          by (metis MCon_imps_sub_Mcon)
        then show ?case
        proof(cases "lIn = prnt")
          case True
          have "prnt \<noteq> l" using ldef
            by (metis hash_inequality)
          moreover have "MTArray x11 x12 = MTArray len' arr'" using iInDef True
            by (metis CompMemType_imps_CompMemJustType MConSubTypes \<open>MCon (MTArray x11 x12) (Memory st) lIn\<close> lsublocs mconPrnt CompMemJustType.simps(2))
          ultimately show ?thesis using True
            by (metis MConPtrsMustBeSubLocs NonChangeM'm iInDef lsublocs mInStd same2 CompMemType.simps(2))
        next
          case False
          then have "CompMemType m x11 x12 (MTArray len' arr') lIn prnt" using iInDef by blast
          then have cp:"CompMemType (Memory st') x11 x12 (MTArray len' arr') lIn prnt" using MTArray.IH[of x11 lIn] mcIn by blast
          have "(hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t iIn)) \<noteq> l"
            by (metis CompMemType_imps_CompMemJustType CompMemTypes_asc MConSubTypes memoryvalue.inject(2) iInDef lOrigin lsublocs mcIn mconlOld option.inject same2
                CompMemJustType.simps(2))
          then have "accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t iIn)) m = accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t iIn)) (Memory st')"
            by (simp add: NonChangeM'm mInStd)
          then have "\<exists>i<lens. \<exists>l. accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some (MPointer l)
              \<and> (l = prnt \<and> MTArray x11 x12 = MTArray len' arr' \<or> CompMemType (Memory st') x11 x12 (MTArray len' arr') l prnt)"
            using False cp iInDef by metis
          then show ?thesis unfolding CompMemType.simps(2)
            using iInDef by blast
        qed
      next
        case (MTValue x2)
        then show ?case
          using compType by auto
      qed
      then show "CompMemType (Memory st') lens subTs (MTArray len' arr') locs prnt" by blast
      show "CompMemType m lens subTs (MTArray len' arr') locs prnt " using a10 by simp
    qed


    have l''MConst':"\<forall>locs lens subTs. CompMemType (Memory st) lens subTs (MTArray len' arr') locs prnt
                          \<and> MCon (MTArray lens subTs) (Memory st) locs \<and> MCon (MTArray lens subTs) m locs \<longrightarrow> MCon (MTArray lens subTs) (Memory st') locs"
    proof intros

      fix locs lens subTs
      assume asm6:"CompMemType (Memory st) lens subTs (MTArray len' arr') locs prnt \<and> MCon (MTArray lens subTs) (Memory st) locs \<and> MCon (MTArray lens subTs) m locs "
      then have asm7:"CompMemType (Memory st) lens subTs (MTArray len' arr') locs prnt" by simp
      have asm8:"MCon (MTArray lens subTs) (Memory st) locs" using asm6 by blast
      have asm9:"MCon (MTArray lens subTs) m locs " using asm6 by blast
      show "MCon (MTArray lens subTs) (Memory st') locs "
      proof(cases "locs = prnt")
        case True
        then show ?thesis
          using MConPtrsMustBeSubLocs_CompMemType lsublocs lsublocs3 prntMconNew asm8 asm7 by blast
      next
        case False
        then have cpMemo:"CompMemType (Memory st) lens subTs (MTArray len' arr') locs prnt"
          using asm6 by blast
        then have asm10:"CompMemType m lens subTs (MTArray len' arr') locs prnt" using compmemst' asm8 by blast
        then have "CompMemType (Memory (st')) lens subTs (MTArray len' arr') locs prnt" using compmemst'
          using asm8 cpMemo by blast
        have "CompMemType m lens subTs (MTArray x memArr) locs p''" using asm10 compType
          by (metis allocateSame compMemTypes_trns lOrigin l_not_toploc_orSub lsublocs nonLocChanged CompMemType.simps(2))
        then have "\<forall>locs' loct. CompMemType m lens subTs loct locs locs' \<and> locs' = p'' \<longrightarrow> loct = (MTArray x memArr)"
          using p''mMcon asm9 asm7
          using CompMemTypeSameLocsSameType by blast
        then show ?thesis using asm9 p''mMcon ldef lOrigin
        proof(induction subTs arbitrary: lens locs)
          case (MTArray x1 subT)
          have "\<forall>i<lens.
           (case accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') of None \<Rightarrow> False
            | Some (MValue val) \<Rightarrow> (case MTArray x1 subT of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon
                (MTArray x1 subT) (Memory st') (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
            | Some (MPointer loc2) \<Rightarrow> (case MTArray x1 subT of MTArray len' arr' \<Rightarrow> MCon (MTArray x1 subT) (Memory st') loc2 | MTValue Types \<Rightarrow> False))"
          proof intros
            fix i'' assume asm1:"i''<lens"
            then obtain ptr where ptrDef:"accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) m = Some (MPointer ptr) \<and> MCon (MTArray x1 subT) m ptr" using MTArray.prems(2)
              by (metis MConArrayPointers MconSameTypeSameAccessWithTyping bot_nat_0.not_eq_extremum less_nat_zero_code)

            show "(case accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st') of None \<Rightarrow> False
            | Some (MValue val) \<Rightarrow> (case MTArray x1 subT of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon
                (MTArray x1 subT) (Memory st') (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i'')))
            | Some (MPointer loc2) \<Rightarrow> (case MTArray x1 subT of MTArray len' arr' \<Rightarrow> MCon (MTArray x1 subT) (Memory st') loc2 | MTValue Types \<Rightarrow> False))"
            proof(cases "ptr = p''")
              case True
              then have sameTp:" (MTArray x1 subT) = (MTArray x memArr)" using MTArray.prems ptrDef asm1 by auto
              then show ?thesis
              proof(cases "(hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) = l")
                case True
                then have "accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st') = Some (MPointer (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))))"
                  using accessL mInStd by auto
                then show ?thesis using sameTp MCondest2 by fastforce
              next
                case False
                then have "accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) m = accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st')"
                  by (simp add: NonChangeM'm mInStd)
                have "\<forall>locs loct. CompMemType m x1 subT loct ptr locs \<and> locs = p'' \<longrightarrow> loct = MTArray x memArr"
                  using CompMemTypeSameLocsSameType ptrDef
                  using MTArray.prems(1) asm1 CompMemType.simps(2) by blast
                moreover have "MCon (MTArray x1 subT) (Memory st') ptr" using MTArray.IH[of x1 ptr] MTArray.prems ptrDef calculation by blast
                ultimately show ?thesis
                  by (metis mtypes.simps(5) memoryvalue.simps(6) Option.option.simps(5) \<open>accessStore (hash locs
                      (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) m = accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory
                      st')\<close> ptrDef)
              qed
            next
              case False
              then have "(hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t
                  i'')) \<noteq> l" using MTArray.prems memoryvalue.inject(2) \<open>accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t
                      i'')) m = Some (MPointer ptr) \<and> MCon (MTArray x1 subT) m ptr\<close> option.inject

                by (metis l_not_toploc_orSub nonLocChanged22)
              then have "accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) m = accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st')"
                by (simp add: NonChangeM'm mInStd)
              have "\<forall>locs loct. CompMemType m x1 subT loct ptr locs \<and> locs = p'' \<longrightarrow> loct = MTArray x memArr"
                using CompMemTypeSameLocsSameType ptrDef
                using MTArray.prems(1) asm1 CompMemType.simps(2) by blast
              moreover have "MCon (MTArray x1 subT) (Memory st') ptr" using MTArray.IH[of x1 ptr] MTArray.prems ptrDef calculation by blast
              ultimately show ?thesis
                by (metis mtypes.simps(5) memoryvalue.simps(6) Option.option.simps(5) \<open>accessStore (hash locs
                    (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) m = accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory
                    st')\<close> ptrDef)
            qed
          qed
          moreover have "lens > 0" using MTArray by force
          moreover have "(\<exists>p. accessStore locs (Memory st') = Some (MPointer p)) \<or> accessStore locs (Memory st') = None"
          proof(cases "locs = l")
            case True
            then show ?thesis
              using accessL mInStd by auto
          next
            case False
            then have "accessStore locs (Memory st') = accessStore locs m"
              by (simp add: NonChangeM'm mInStd)
            then show ?thesis using MTArray(3) calculation(2) by simp
          qed

          ultimately show ?case using MCon.simps(2)[of lens "MTArray x1 subT" "Memory st'" locs] by simp
        next
          case (MTValue x')
          have "\<forall>i<lens.
           (case accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') of None \<Rightarrow> False
            | Some (MValue val) \<Rightarrow> (case MTValue x' of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon
                (MTValue x') (Memory st') (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
            | Some (MPointer loc2) \<Rightarrow> (case MTValue x' of MTArray len' arr' \<Rightarrow> MCon (MTValue x') (Memory st') loc2 | MTValue Types \<Rightarrow> False))"
          proof(intros)
            fix i'' assume asm1:"i''<lens"
            then obtain ptr where ptrDef:"accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t
                i'')) (m) = Some(MValue ptr) \<and> MCon (MTValue x') m (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i''))"
              using MCon_sub_MTVal_imps_val MTValue.prems(2) MconSameTypeSameAccessWithTyping by presburger
            then have "(hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) \<noteq> l"
              using allocateSame lOrigin l_not_toploc_orSub nonLocChanged by fastforce
            then have "accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (m) = accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st')"
              by (simp add: NonChangeM'm mInStd)
            then show "case accessStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st') of None \<Rightarrow> False
            | Some (MValue val) \<Rightarrow> (case MTValue x' of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon
                (MTValue x') (Memory st') (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i'')))
            | Some (MPointer loc2) \<Rightarrow> (case MTValue x' of MTArray len' arr' \<Rightarrow> MCon (MTValue x') (Memory st') loc2 | MTValue Types \<Rightarrow> False)"
              using ptrDef
              by (metis mtypes.simps(6) memoryvalue.simps(5) Option.option.simps(5) MCon.simps(1))
          qed
          moreover have "lens > 0" using MTValue by fastforce
          moreover have "(\<exists>p. accessStore locs (Memory st') = Some (MPointer p)) \<or> accessStore locs (Memory st') = None"
          proof(cases "locs = l")
            case True
            then show ?thesis
              using accessL mInStd by auto
          next
            case False
            then have "accessStore locs (Memory st') = accessStore locs m"
              by (simp add: NonChangeM'm mInStd)
            then show ?thesis using MTValue(2) calculation(2) by simp
          qed
          ultimately show ?case using MCon.simps(2)[of lens "MTValue x'" "Memory st'" locs] by simp
        qed
      qed
    qed
    have mcf:"\<forall>x11 x12 x3. CompMemType (Memory st) x11 x12 (MTArray len subT) x3 l'' \<and> MCon (MTArray x11 x12) (Memory st) x3
          \<longrightarrow> CompMemType m x11 x12 (MTArray len subT) x3 l''"
    proof(intros)
      fix x11 x12 x3
      assume asm3:"CompMemType (Memory st) x11 x12 (MTArray len subT) x3 l'' \<and> MCon (MTArray x11 x12) (Memory st) x3"
      then show "CompMemType m x11 x12 (MTArray len subT) x3 l''"
      proof(induction x12 arbitrary: x11 x3)
        case (MTArray x1 x12)
        then obtain i'' ptr where ptrDef:"(i''<x11 \<and> accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) (Memory st) = Some
            (MPointer ptr) \<and> (ptr = l'' \<and> MTArray x1 x12 = MTArray len subT \<or> CompMemType (Memory st) x1 x12 (MTArray len
            subT) ptr l''))"
          unfolding CompMemType.simps by blast
        then show ?case
        proof(cases "ptr = l''")
          case True
          then show ?thesis
            by (metis CompMemType.simps(2) MTArray.prems existingLocation_imps_allLocs_same limitSt nle_le nonLocChanged22 option.discI
                ptrDef)
        next
          case False
          then have " CompMemType (Memory st) x1 x12 (MTArray len subT) ptr l''" using ptrDef by simp
          moreover have "MCon (MTArray x1 x12) (Memory st) ptr"
            using MCon_imps_sub_Mcon MTArray.prems ptrDef by blast
          ultimately show ?thesis using MTArray.IH[of x1 ptr]
            by (metis limitSt nat_le_linear nonLocChanged22 not_Some_eq ptrDef CompMemType.simps(2))
        qed
      next
        case (MTValue x)
        then show ?case by simp
      qed
    qed


    have BT3:"\<forall>locs tp x t. \<not>LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow>
        \<not>CompMemType (Memory (st')) x t tp (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) locs
                                                                  \<and> \<not>TypedMemSubPrefPtrs (Memory (st')) x t (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) locs"
      using CompMemType_imps_TypedMemSubPrefPtrs LSubPrefL2_def SubPtrs_top selfPoint2 by blast

    have mconL''New:"MCon (MTArray len subT) (Memory st') l''" using lsublocs3
    proof(cases "prnt = l''")
      case True
      then have notComp:"\<not>CompMemType (Memory (st)) len subT (MTArray len' arr') l'' prnt"
        using lsublocs BothMConImpsNotCompMemType[of len subT "Memory st" l'' "(MTArray len' arr')"] lsublocs3
        using BothMConImpsNotCompMemType t7 by blast
      then have sameTypes:"len = len' \<and> arr' = subT " using lsublocs3 by simp
      then show ?thesis using prntMconNew True
        using lsublocs by blast
    next
      case False
      then have "CompMemType (Memory (st)) len subT (MTArray len' arr') l'' prnt" using lsublocs3 by simp
      then have a:"CompMemType (Memory (st')) len subT (MTArray len' (MTArray x memArr)) l'' prnt" using compmemst' lsublocs
        using t7 by blast
      then show ?thesis using False l''MConst' t7
        using \<open>CompMemType (Memory st) len subT (MTArray len' arr') l'' prnt\<close> l''mMcon by blast
    qed

    have NonChangeM'mT:"\<forall>locs. accessTypeStore locs m = accessTypeStore locs m'"
      using 15(5) unfolding accessStore_def updateStore_def accessTypeStore_def by auto

    have sameTypeAccess:" \<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<or> locs =
        (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow>
     accessTypeStore locs (Memory st) = accessTypeStore locs m"
      using 15(4) unfolding cps2m_def
      using cps2mSingleChange_Typed[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t "(Storage st (Address env))" " (snd (allocate (Memory st)))" x m ]
        allocateTypeSameAccess by metis

    have sameTypeAccess2:" \<forall>locs. \<not> TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x
        memArr) \<or> locs = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow>
     accessTypeStore locs (Memory st) = accessTypeStore locs m"
      using 15(4) unfolding cps2m_def
      using cps2mSingleChange_typedPref_typed[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t "(Storage st (Address env))" " (snd (allocate (Memory st)))" x m ]
        allocateTypeSameAccess memArrDef compatible_TypedStoSubpref_imps_TypedMemSubPref[OF 15(3)]
      by (metis sameTypeAccess)


    have tps:"\<forall>destl'.
     TypedMemSubPref destl' (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x memArr) \<longrightarrow>
     (\<exists>stt. CompMemType m x memArr stt (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) destl' \<and>
         (case stt of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some parent_arr
          | MTValue pval \<Rightarrow> accessTypeStore destl' m = Some (MTValue pval)))"
      using 15(3,4) memArrDef unfolding cps2m_def
      using cps2m_TypeCompChange[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t "(Storage st (Address env))" "(snd (allocate (Memory st)))" x m]
      by simp

    have selfPointMem:"\<forall>l l'.
     TypedMemSubPref l (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x memArr) \<and> accessStore l m = Some (MPointer l') \<longrightarrow> l' = l"
      using selfPoint compatible_TypedStoSubpref_imps_TypedMemSubPref[OF 15(3)] memArrDef
      using selfPoint_root by presburger
    have topIndexType:" \<forall>i<x. accessTypeStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some memArr" using memArrDef
      using "15"(3,4) cps2m_TypeCompChangeIndexs cps2m_def by auto
    have a32Mem:"\<forall>locs.
     \<not> TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x memArr) \<longrightarrow>
     accessStore locs (Memory st) = accessStore locs m"
      using a32 compatible_TypedStoSubpref_imps_TypedMemSubPref[OF 15(3)] memArrDef
      using nonLocChanged22 by blast
    have subPrefM:"subPrefixStructuralConsistency (m)"
      using cpm2m_subPrefixPersist[OF _ _ _ sameTypeAccess _ sameTypeAccess2 tps MCondest selfPointMem topIndexType nonLocChanged22 a32Mem]
        \<open>accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (snd (allocate (Memory st))) = None\<close> allocateSame 2(1)
      unfolding TypeSafe_def by simp

    have nonLocChanged_TypedSafe:"\<forall>loc. \<not> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))
                                        \<longrightarrow> accessTypeStore loc (Memory st') = accessTypeStore loc (Memory st)"
    proof -
      have "\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<or> locs =
          (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow> accessTypeStore locs (snd (allocate (Memory st))) =
          accessTypeStore locs m"
        using 15(4,5,6) cps2mSingleChange_Typed[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t _ " (snd (allocate (Memory st)))" x m ]
          cps2m_def[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" x t _ " (snd (allocate (Memory st)))" ] by simp
      then have "\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<or> locs =
          (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow> accessTypeStore locs (snd (allocate (Memory st))) =
          accessTypeStore locs m'"
        using 15(6,5) unfolding accessTypeStore_def updateStore_def by force
      then show "\<forall>loc. \<not> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow> accessTypeStore loc (Memory st') = accessTypeStore loc (Memory st)"
        using allocateTypeSameAccess mInStd by metis
    qed

    have nonLocChanged_MemSafe:"\<forall>loc. \<not> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<and> loc \<noteq> l
                                      \<longrightarrow> accessStore loc (Memory st') = accessStore loc (Memory st)"
      using mInStd nonLocChanged allocateSame mInStd 15(5) unfolding updateStore_def accessStore_def
      by (metis accessStore_def nonLocChanged2)

    show ?thesis unfolding TypeSafe_def StateInvariant_def
    proof intros
      show "AddressTypes (Accounts st')" using 2(1) unfolding TypeSafe_def using 15 by simp
    next
      show "unique_locations (Denvalue env)" using 2(1) unfolding TypeSafe_def by simp
    next
      have a0:" compPointers (Stack st) (Denvalue env)" using 2(1) unfolding TypeSafe_def by blast
      then show "compPointers (Stack st') (Denvalue env)" using sameStack sameStorage by simp
    next
      show "safeContract (Accounts st') (Storage st')" using sameStorage 2(1) 15 unfolding TypeSafe_def safeContract_def by auto
    next
      show "balanceTypes (Accounts st')" using 15 using 2(1) unfolding TypeSafe_def by simp
    next
      have "envAddressesWellFormed env" using 2(1) unfolding TypeSafe_def by simp
      then show "addressFormat (Address env)" and "addressFormat (Sender env)" by simp+
    next
      show "svalueTypes (Svalue env)" using 2(1) unfolding TypeSafe_def by simp
    next
      have *:"((\<forall>tloc loc. Toploc (Stack st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Stack st) = None) \<and>
            (\<forall>loc y. accessStore loc (Stack st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Stack st). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))) "
        using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by simp
      have **:"Toploc (Stack st) = Toploc (Stack st')" using 15 unfolding updateStore_def by auto
      show "lessThanTopLocs (Stack st')" unfolding lessThanTopLocs_def
      proof intros

        fix tloc loc
        assume h1:"Toploc (Stack st') \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
        then have "Toploc (Stack st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)" using ** by simp
        then show "accessStore loc (Stack st') = None" using *
          by (simp add: sameStack)
      next
        fix loc y
        assume h1:" accessStore loc (Stack st') = Some y"
        then show "\<exists>tloc<Toploc (Stack st'). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)" using ** *
          by (metis sameStack)
      qed
    next
      show "lessThanTopLocs cd" using 2(1) unfolding TypeSafe_def by simp
    next
      have a10:"Toploc (snd (allocate (Memory st))) = Toploc m"
        using cps2mTopLocSame[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t "(Storage st (Address env))" "(snd (allocate
            (Memory st)))" x m] 15(4) mInStd unfolding cps2m_def by fastforce
      then have a12:"Toploc m = Toploc m'" using 15(5) unfolding updateStore_def by auto
      have a15:"lessThanTopLocs (Memory st)" using 2 unfolding TypeSafe_def by simp
      have tloc:"Toploc (Memory st) < Toploc (snd (allocate (Memory st)))" unfolding allocate_def by simp
      show "lessThanTopLocs (Memory st')" unfolding lessThanTopLocs_def
      proof intros
        fix tloc loc
        assume b10: "Toploc (Memory st') \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
        then have b20:"Toploc (Memory st) \<le> tloc" using a10 tloc a12
          using mInStd by force

        then show "accessStore loc (Memory st') = None "
          by (metis (no_types, lifting) LSubPrefL2_def MemLSubPrefTransitive NonChangeM'm \<open>\<exists>x. accessStore l (Memory st) =
              Some x\<close> a10 a12 allocateSame antisym_conv2 b10 hash_inequality
              hash_suffixes_associative hashesIntSame limitSt mInStd nonLocChanged option.discI order_less_le_trans tloc)
      next
        fix loc y
        assume "accessStore loc (Memory st') = Some y "
        then show "\<exists>tloc<Toploc (Memory st'). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
          by (metis NonChangeM'm \<open>\<exists>x. accessStore l (Memory st) = Some x\<close> a10 a12 allocateSameAccess limitSt1 mInStd nonLocChanged order_less_trans tloc)
      qed
    next
      show "typeCompat (Denvalue env) (Stack st') (Memory st') (Storage st' (Address env)) cd"
        unfolding typeCompat_def
      proof intros
        fix tLook lLook
        assume inDen:" (tLook, lLook) |\<in>| fmran (Denvalue env)"
        show " denvalueCon (Stack st') (Memory st') (Storage st' (Address env)) cd tLook lLook"
        proof(cases lLook)
          case (Stackloc x1)
          then obtain a where adef:"accessStore x1 (Stack st') = Some a" using inDen Stackloc 2(1) unfolding TypeSafe_def typeCompat_def using sameStack nonChangedStack by fastforce
          then show ?thesis
          proof(cases "a")
            case (KValue x1)
            then show ?thesis using Stackloc adef inDen Stackloc 2(1) sameStack nonChangedStack unfolding TypeSafe_def typeCompat_def
              by (metis (no_types, lifting) denvalue.simps(5) Option.option.simps(5) stackvalue.simps(17) )
          next
            case (KCDptr x2)
            then show ?thesis using Stackloc adef inDen Stackloc 2(1) sameStack nonChangedStack unfolding TypeSafe_def typeCompat_def
              by (metis (no_types, lifting) denvalue.simps(5) Option.option.simps(5) stackvalue.simps(18) )
          next
            case (KMemptr x3)
            then have "\<exists>struct. tLook = type.Memory struct" using Stackloc adef inDen Stackloc 2(1) KMemptr sameStack unfolding TypeSafe_def typeCompat_def by (cases tLook;force+)
            then obtain struct where structdef:"tLook = type.Memory struct" by blast

            then have mcOld:"MCon struct (Memory st) x3" using 2(1) unfolding TypeSafe_def typeCompat_def
              using Stackloc adef inDen KMemptr sameStack by (auto split:type.splits denvalue.splits stackvalue.splits option.splits)
            then have mcM:"MCon struct m x3" using PreExistMconNotChangeByToploc limitSt limitSt1 nonLocChanged22
              by auto
            have structss:"(case struct of
     MTArray len arr \<Rightarrow>
       (\<forall>i<len. accessTypeStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr)
     | MTValue val \<Rightarrow> accessTypeStore x3 (Memory st) = Some (MTValue val))"
              using 2(1) inDen KMemptr Stackloc structdef adef 15(6)
              unfolding TypeSafe_def denvalueTypeCorrectness_def by simp
            then have structss:"(case struct of
     MTArray len arr \<Rightarrow>
       (\<forall>i<len. accessTypeStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr)
     | MTValue val \<Rightarrow> accessTypeStore x3 (Memory st) = Some (MTValue val))"
              by (metis (no_types, lifting))
            have nonLocChanged_TypedSafe:"\<forall>loc. \<not> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))
                                        \<longrightarrow> accessTypeStore loc m = accessTypeStore loc (Memory st)"
            proof -
              have "\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<or> locs =
                  (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow> accessTypeStore locs (snd (allocate (Memory st)))
                  = accessTypeStore locs m"
                using 15(4,5,6) cps2mSingleChange_Typed[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t "(Storage st (Address env))" " (snd (allocate (Memory st)))" x m ]
                  cps2m_def[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" x t "(Storage st (Address env))" " (snd (allocate (Memory st)))" ] by simp
              then show "\<forall>loc. \<not> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow> accessTypeStore loc m = accessTypeStore loc (Memory st)"
                using allocateTypeSameAccess mInStd by metis
            qed

            then have "accessTypeStore x3 (Memory st) = accessTypeStore x3 m"
              using limitSt limitSt1 mcOld
              by (metis AllPtrsNotTop_MCon lessThanTopLocs_def nat_le_linear)
            moreover have eq2:"\<forall>i::nat. accessTypeStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = accessTypeStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (m)"
              using nonLocChanged_TypedSafe limitSt limitSt1 mcOld AllPtrsNotTop_MCon lessThanTopLocs_def
              by (metis MemLSubPrefL2_specific_imps_general nat_le_linear)
            ultimately have structss:"(case struct of
     MTArray len arr \<Rightarrow>
       (\<forall>i<len. accessTypeStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some arr)
     | MTValue val \<Rightarrow> accessTypeStore x3 m = Some (MTValue val))" using structss by presburger

            have "accessTypeStore l (Memory st) = Some (MTArray x memArr)"
              using lInfo 15 nonLocChanged memArrDef by simp
            then have accl:"accessTypeStore l (m) = Some (MTArray x memArr)"
              using nonLocChanged_TypedSafe
              using l_not_toploc_orSub by auto
            have "MCon struct (Memory st') x3"
              using cpm2m_singleLChange[OF mcM structss _ _ _ MCondest2 subPrefM] 15(5) mInStd
                NonChangeM'm accessL accl memArrDef
              by (metis lOrigin l_not_toploc_orSub nonLocChanged22)

            then show ?thesis using structdef KMemptr Stackloc adef inDen Stackloc 2(1) unfolding TypeSafe_def typeCompat_def by simp

          next
            case (KStoptr x4)
            then show ?thesis using Stackloc
                adef sameStorage inDen Stackloc KStoptr 2(1) nonChangedStack sameStack
              unfolding TypeSafe_def typeCompat_def
                apply(cases tLook) by fastforce+
          qed
          next
          case (Storeloc x2)
          then show ?thesis using sameStorage inDen 2(1) unfolding TypeSafe_def typeCompat_def by (cases tLook; force)
        qed
      qed
      then have "typeCompat (Denvalue env) (Stack st) (Memory st') (Storage st' (Address env)) cd " using sameStack by simp
      next
      have "Accounts st'= Accounts st" using 15 by auto
      then show "fullyInitialised env (Accounts st') (Stack st')" using 2(3) unfolding fullyInitialised_def
          using sameStack by presburger
     next
      show "denvalueTypeCorrectness env (Stack st') (Memory st') "
          unfolding denvalueTypeCorrectness_def
      proof(intros)
        fix t2 l2 ptr_loc sub_loc
        assume *:"(type.Memory t2, Stackloc l2) |\<in>| fmran (Denvalue env) \<and> accessStore l2 (Stack st') = Some (KMemptr ptr_loc)"

        show "case t2 of
       MTArray len arr \<Rightarrow>
       (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr)
     | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st') = Some (MTValue val)"
        proof -
          have sameACC:"accessStore l2 (Stack st') = accessStore l2 (Stack st)"
              using nonChangedStack * 15(5,6) unfolding accessStore_def updateStore_def by simp
          then have mcOld:"MCon t2 (Memory st) ptr_loc" using * by (metis 2(1) sameMemTSafe)
          then have old:"(case t2 of
                         MTArray len arr \<Rightarrow>
         (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr)
       | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st) = Some (MTValue val))"
              using sameACC 2(1) * TypeSafe_def denvalueTypeCorrectness_def by fastforce

          have inDenvalue:"(type.Memory t2, Stackloc l2) |\<in>| fmran (Denvalue env)" using * by simp

          then show ?thesis
          proof(cases t2)
            case (MTArray x11 x12)
            then have mcOld:"MCon (MTArray x11 x12) (Memory st) ptr_loc" using mcOld by blast
            have old':"(\<forall>i<x11. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some x12)"
                using old MTArray by simp

            have conc0:"(\<forall>i<x11. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some x12)"
            proof -
              have o:"\<forall>i<x11. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some x12" using old' by blast
              then have "\<forall>i<x11. \<exists>v. accessStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some v"
                  using 2(1) unfolding TypeSafe_def SomeValSomeTyp_def by auto
              then have "\<forall>i<x11. \<not> LSubPrefL2 (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))"
                  using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by fastforce
              then show ?thesis using nonLocChanged_TypedSafe o nonLocChanged_MemSafe old' by auto
            qed
            then show ?thesis using MTArray by auto
            next
            case (MTValue x2)
            have "\<not> LSubPrefL2 ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))"
                using typeSafe_noDenElementOverToploc_mem[OF 2(1) inDenvalue] * sameACC
                using LSubPrefL2_def MemLSubPrefTransitive by metis
            then have "accessTypeStore ptr_loc (Memory st') = accessTypeStore ptr_loc (Memory st)"
                using "15"(6) allocateTypeSameAccess cpm2mSingleChange_Typed cpm2m_def mInStd
                using nonLocChanged_TypedSafe by blast
            then show ?thesis using MTValue old by simp
          qed
        qed
      qed
      next
      show "subPrefixStructuralConsistency (Memory st')"
          unfolding subPrefixStructuralConsistency_def
      proof intros
        fix locs tp
        assume in1:" accessTypeStore locs (Memory st') = Some tp "
        have sameTy:"\<forall>locs. accessTypeStore locs m = accessTypeStore locs (Memory st') "
            using mInStd by (metis NonChangeM'mT)
        then have in2:"accessTypeStore locs m = Some tp " using in1 by simp
        show "case accessStore locs (Memory st') of None \<Rightarrow> False
              | Some (MValue v) \<Rightarrow> \<exists>val. MCon tp (Memory st') locs \<and> tp = MTValue val \<and> accessTypeStore locs (Memory st') = Some tp
              | Some (MPointer p) \<Rightarrow>
                 \<exists>len arr.
                    MCon tp (Memory st') p \<and>
                    tp = MTArray len arr \<and>
                    (\<forall>i<len. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr)"
        proof(cases "locs = l")
          case True
          have "accessTypeStore l (Memory st) = Some (MTArray x memArr)"
              using lInfo 15 nonLocChanged memArrDef by auto
          then have accl:"accessTypeStore l (m) = Some (MTArray x memArr)"
              using nonLocChanged_TypedSafe l_not_toploc_orSub
              using sameTypeAccess by auto
          then have tpDef:"tp = MTArray x memArr"
              using sameTy True in1 by simp
          then have ptr:"accessStore locs (Memory st') = Some (MPointer (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))))"
              using mInStd True by (metis accessL)
          have sameAccm:"accessStore l m = accessStore l (Memory st)"
              using l_not_toploc_orSub nonLocChanged22 by fastforce
          moreover have " MCon tp (Memory st') (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))"
              using MCondest2 tpDef by blast
          moreover have "(\<forall>i<x. accessTypeStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some memArr)"
              using tpDef ptr subPrefM sameAccm accl unfolding subPrefixStructuralConsistency_def
              using sameTy topIndexType by presburger
          moreover have "
         (\<forall>v. accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (Memory st') = Some (MPointer v)
                \<longrightarrow> accessTypeStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (Memory st') = Some (MTArray x memArr))"
              using LSubPrefL2_def selfPoint2 by blast
          ultimately show ?thesis using True tpDef ptr by auto
          next
          case False
          then have sameACC:"accessStore locs m = accessStore locs (Memory st')"
              using mInStd NonChangeM'm by simp
          then have in3:"(case accessStore locs m of None \<Rightarrow> False | Some (MValue v) \<Rightarrow> \<exists>val. MCon tp m locs
              \<and> tp = MTValue val \<and> accessTypeStore locs m = Some tp
      | Some (MPointer p) \<Rightarrow>
          \<exists>len arr.
             MCon tp m p \<and>
             tp = MTArray len arr \<and>
             (\<forall>i<len. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some arr) )"
              using subPrefM in2 unfolding subPrefixStructuralConsistency_def by blast
          then show ?thesis
          proof(cases "accessStore locs m")
            case None
            then show ?thesis using in3 sameACC by simp
            next
            case (Some a)
            then show ?thesis
            proof(cases a)
              case (MValue x1)
              then obtain val where " MCon tp m locs \<and> tp = MTValue val \<and> accessTypeStore locs m = Some tp"
                  using in3 Some by auto
              moreover have "MCon tp (Memory st') locs" using sameACC calculation by auto
              ultimately show ?thesis using sameACC Some MValue sameTy
                  by (auto split:option.splits)
              next
              case (MPointer x2)
              have "accessTypeStore l (Memory st) = Some (MTArray x memArr)"
                  using lInfo 15 nonLocChanged memArrDef by auto
              then have accl:"accessTypeStore l (m) = Some (MTArray x memArr)"
                  using nonLocChanged_TypedSafe l_not_toploc_orSub
                  using sameTypeAccess by auto
              then obtain len arr where s:"MCon tp m x2 \<and> tp = MTArray len arr \<and>
                         (\<forall>i<len. accessTypeStore (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some arr)"
                  using Some in3 MPointer by auto
              then have mcM:"MCon tp m x2" by auto
              have lAcc:"updateStore l (MPointer (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))) m = Memory st'"
                  using 15(5) mInStd by blast
              have "MCon tp (Memory st') x2"
                  using cpm2m_singleLChange[OF mcM _ lAcc _ accl MCondest2 subPrefM]
                    mInStd NonChangeM'm accessL lOrigin l_not_toploc_orSub nonLocChanged22 s
                  by auto

              moreover have "(\<forall>i<len. accessTypeStore (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr)"
                  using s sameTy by simp

              ultimately show ?thesis using Some MPointer sameACC sameTy s
                  by (auto split:option.splits)
            qed
          qed
        qed
      qed
      next
      have old:"(\<forall>locs. (\<exists>t. accessStore locs (Memory st) = Some t) = (\<exists>tt. accessTypeStore locs (Memory st) = Some tt))"
          using 2(1) unfolding TypeSafe_def SomeValSomeTyp_def by blast
      have somesome:"\<forall>destl'. TypedMemSubPref destl' (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x memArr)
            \<longrightarrow> (\<exists>t. accessStore destl' m = Some t) = (\<exists>tt. accessTypeStore destl' m = Some tt)"
          using 15(3,4) unfolding cps2m_def using cps2m_TypeCompChange_somesome[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t _ "(snd (allocate (Memory st)))" x m]
          using memArrDef by blast
      have a30T:"\<forall>locs. \<not> TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x memArr)
                \<longrightarrow> accessTypeStore locs (Memory st) = accessTypeStore locs m"
          using 15(3,4) unfolding cps2m_def using cps2mSingleChange_typedPref_typed[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t _ " (snd (allocate (Memory st)))" x m ]
            mInStd allocateTypeSameAccess memArrDef
          by (metis (no_types, lifting) ext compatible_TypedStoSubpref_imps_TypedMemSubPref_neg cps2mSingleChange_Typed)
      have lIs:"\<exists>x. accessStore l (Memory st) = Some x" using lInfo by (auto split:option.splits)
      show "SomeValSomeTyp (Memory st')"unfolding SomeValSomeTyp_def
      proof intros
        fix locs
        show "(\<exists>t. accessStore locs (Memory st') = Some t) = (\<exists>tt. accessTypeStore locs (Memory st') = Some tt) "
        proof(cases "TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x memArr)")
          case True
          then have ss:"(\<exists>t. accessStore locs m = Some t) = (\<exists>tt. accessTypeStore locs m = Some tt)"
              using somesome by simp
          then show ?thesis
          proof(cases "locs = l")
            case True
            then show ?thesis using lInfo NonChangeM'mT accessL mInStd ss
                using lIs l_not_toploc_orSub nonLocChanged22 by auto
            next
            case False
            then show ?thesis using ss NonChangeM'mT NonChangeM'm mInStd by simp
          qed
          next
          case False
          then have acc1:"accessStore locs (Memory st) = accessStore locs m"
              by (metis False memArrDef a32Mem)
          have acc2:"accessTypeStore locs (Memory st) = accessTypeStore locs (Memory st')"
              using a30T False mInStd NonChangeM'mT by simp
          show ?thesis
          proof(cases "locs = l")
            case True
            then show ?thesis using lInfo acc2 accessL mInStd by force
            next
            case False
            then have "accessStore locs m = accessStore locs (Memory st')"
                using mInStd NonChangeM'm by auto
            then show ?thesis using old acc1 acc2 by metis
          qed
        qed
      qed
      next
      fix locs tt
      assume a1:" accessTypeStore locs (Memory st) = Some tt"
      then have some:"\<exists>v. accessStore locs (Memory st) = Some v"
          using 2(1) unfolding TypeSafe_def SomeValSomeTyp_def by blast
      have a30T:"\<forall>locs. \<not> TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x memArr)
                \<longrightarrow> accessTypeStore locs (Memory st) = accessTypeStore locs m"
          using 15(3,4) unfolding cps2m_def using cps2mSingleChange_typedPref_typed[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t _ " (snd (allocate (Memory st)))" x m ]
            mInStd allocateTypeSameAccess memArrDef
          by (metis (no_types, lifting) ext compatible_TypedStoSubpref_imps_TypedMemSubPref_neg cps2mSingleChange_Typed)
      show " accessTypeStore locs (Memory st') = Some tt"
      proof(cases "TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) (MTArray x memArr)")
        case True
        then show ?thesis using some a1
            by (metis le_refl limitSt option.distinct(1) typedPrefix_imp_SubPref)
        next
        case False
        then have acc1:"accessStore locs (Memory st) = accessStore locs m"
            using a30 mInStd
            by (metis False memArrDef a32Mem)
        have acc2:"accessTypeStore locs (Memory st) = accessTypeStore locs (Memory st')"
            using a30T False mInStd NonChangeM'mT by simp
        show ?thesis
        proof(cases "locs = l")
          case True
          then show ?thesis using lInfo acc2 accessL mInStd a1 by argo
          next
          case False
          then show ?thesis using acc1 acc2 a1 by auto
        qed
      qed
      next
      show "\<And>locs v. accessStore locs (Memory st) = Some (MPointer v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MPointer v')"
          by (metis accessL le_refl limitSt mInStd nonLocChanged2 option.distinct(1))
      next
      show "\<And>locs v. accessStore locs (Memory st) = Some (MValue v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MValue v')"
        using NonChangeM'm lOrigin limitSt mInStd nonLocChanged22
        by (metis dual_order.refl memoryvalue.distinct(1) option.distinct(1) option.inject)
      next
      show " \<And>i loc. i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<Longrightarrow> accessStore loc
          (Memory st) = None \<Longrightarrow> accessStore loc (Memory st') = None"
          using lOrigin limitSt nonLocChanged2
          by (metis (no_types, lifting) LSubPrefL2_def MemLSubPrefTransitive Read_Show_nat'_id hash_flatten_right hash_inequality nat_less_le option.distinct(1))
      next
      have a10:"Toploc (snd (allocate (Memory st))) = Toploc m"
          using cps2mTopLocSame[of p "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))" t "(Storage st (Address env))" "(snd (allocate (Memory st)))" x m]
            15(4) mInStd unfolding cps2m_def by fastforce
      moreover have a12:"Toploc m = Toploc m'" using 15(5) unfolding updateStore_def by auto
      moreover have tloc:"Toploc (Memory st) < Toploc (snd (allocate (Memory st)))" unfolding allocate_def by simp
      ultimately show "Toploc (Memory st) \<le> Toploc (Memory st')"
          using mInStd by auto
    qed
  qed
qed

text \<open>Assignment case 16: a storage mapping assigned to a storage pointer on the stack: the stack now points to the same mapping.\<close>

lemma TypeSafe_Assign_16:
  assumes "TypeSafe env (Accounts st) (Stack st) (Memory st) (Storage st) cd"
    and "stmt (ASSIGN lv ex) env cd st = Normal ((), st')"
    and "fullyInitialised env (Accounts st) (Stack st)"
    and "expr ex env cd (st\<lparr>state.Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>) (state.Gas st - costs (ASSIGN lv
        ex) env cd st) = Normal ((KStoptr p, type.Storage (STMap t g')), g)"
    and "lexp lv env cd (st\<lparr>state.Gas := g\<rparr>) g = Normal((LStackloc l, type.Storage t'),t'')"
    and "t' = (STMap t g')"
    and "st' = st\<lparr>state.Gas := t'', Stack := updateStore l (KStoptr p) (Stack st)\<rparr>"
  shows "StateInvariant env st st' cd"
proof -
  let ?case = "StateInvariant env st st' cd"
  note 2 = assms(1-3)
  note 16 = assms(4-7)
  then have stackChanged:"\<forall>l'. l' \<noteq> l \<longrightarrow> accessStore l' (Stack st) = accessStore l' (Stack st')" unfolding updateStore_def accessStore_def by simp
  have t'InDen:"(type.Storage t', Stackloc l) |\<in>| fmran (Denvalue env)" using lexpStackloc_imps_inDen[OF 16(2)] by blast
  then have lDen:"\<forall>t'. (t', Stackloc l) |\<in>| fmran (Denvalue env) \<longrightarrow> t'= (type.Storage (STMap t g'))" using 16 2(1) unfolding TypeSafe_def unique_locations_def by auto

  have pOrigin:"SCon (STMap t g') (extractValueType (KStoptr p)) (Storage (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>) (Address env)) \<and>
      (\<exists>xx. KStoptr p = KStoptr xx) \<and>
      (\<exists>stloc tp'' .
          (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue env) \<and>
          (tp'' = (STMap t g') \<and> KStoptr p = KStoptr stloc \<or> extractValueType (KStoptr p) \<noteq> stloc \<and> CompStoType tp'' (STMap t g') stloc (extractValueType (KStoptr p))))"
    using 2(1) 16(1) 2(3) using
      exprTypeconInduct(3)[of ex env cd "(st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>)" "(state.Gas st - costs (ASSIGN lv ex) env cd st)" "KStoptr p" ]
    by (auto split:type.splits if_splits )
  obtain pParent pParentT where
    pOrigin:"SCon (STMap t g') (extractValueType (KStoptr p)) (Storage (st\<lparr>Gas := state.Gas st - costs (ASSIGN lv ex) env cd st\<rparr>) (Address env))
        \<and>(type.Storage pParentT, Storeloc pParent) |\<in>| fmran (Denvalue env) \<and>
          (pParentT = (STMap t g') \<and> KStoptr p = KStoptr pParent \<or> extractValueType (KStoptr p) \<noteq> pParent \<and>
              CompStoType pParentT (STMap t g') pParent (extractValueType (KStoptr p)))"
    using pOrigin by auto
  have a0: "compPointers (Stack st) (Denvalue env)" using 2(1) unfolding TypeSafe_def by simp
  then have pParentRelations:"(\<forall>tp2 l2 l2' stl2.
      (type.Storage tp2, l2) |\<in>| fmran (Denvalue env) \<and>

      (l2 = Stackloc l2' \<and> accessStore l2' (Stack (st)) = Some (KStoptr stl2) \<or> l2 = Storeloc stl2) \<longrightarrow>
      (if TypedStoSubpref stl2 pParent pParentT then CompStoType pParentT tp2 pParent stl2 else if TypedStoSubpref pParent stl2 tp2 then CompStoType tp2 pParentT stl2 pParent else True))"
    using compPointers_def pOrigin by blast
  have pSCon:"SCon (STMap t g') (extractValueType (KStoptr p)) (Storage (st) (Address env))" using pOrigin by force

  \<comment> \<open>All locations that reach \<open>p\<close> have parent type \<open>MTArray x t\<close>, and likewise for all locations below \<open>p\<close>\<close>
  have pRelations:"(\<forall>tp2 l2 l2' stl2 .
  (type.Storage tp2, l2) |\<in>| fmran (Denvalue env) \<and>
  ((l2 = Stackloc l2' \<and> accessStore l2' (Stack st) = Some(KStoptr stl2)) \<or> (l2 = Storeloc stl2))
   \<longrightarrow>
  (if TypedStoSubpref p stl2 tp2 then CompStoType tp2 (STMap t g') stl2 p
   else if TypedStoSubpref stl2 p (STMap t g') then CompStoType (STMap t g') tp2 p stl2
   else True))"
  proof intros
    fix tp2 l2 l2' stl2
    assume in1:"(type.Storage tp2, l2) |\<in>| fmran (Denvalue env) \<and> (l2 = Stackloc l2' \<and> accessStore l2' (Stack st) = Some (KStoptr stl2) \<or> l2 = Storeloc stl2)"

    show "if TypedStoSubpref p stl2 tp2 then CompStoType tp2 (STMap t g') stl2 p else if TypedStoSubpref stl2 p (STMap t g') then CompStoType (STMap t g') tp2 p stl2 else True"
    proof(cases "l2 = Stackloc l2'")
      case StL2:True

      have "SCon pParentT pParent (Storage st (Address env))" using pOrigin using 2(1) unfolding TypeSafe_def typeCompat_def by force
      have prnt:" pParentT = (STMap t g') \<and> KStoptr p = KStoptr pParent \<or> extractValueType (KStoptr p) \<noteq> pParent \<and>
          CompStoType pParentT (STMap t g') pParent (extractValueType (KStoptr p))"
        using pOrigin by simp
      then have comp:"(if TypedStoSubpref stl2 pParent pParentT then CompStoType pParentT tp2 pParent stl2
                    else if TypedStoSubpref pParent stl2 tp2 then CompStoType tp2 pParentT stl2 pParent else True)"
        using pParentRelations in1 StL2 prnt by force
      then show ?thesis
      proof(cases "TypedStoSubpref p stl2 tp2")
        case pToStl2:True
        then show ?thesis
        proof(cases "pParentT = (STMap t g')")
          case True
          then have cc1:"KStoptr p = KStoptr pParent " using prnt
            using comp_stotype_same_type_same_loc by blast
          then have cc2:"TypedStoSubpref pParent stl2 tp2" using pToStl2 by auto
          then have "CompStoType tp2 (STMap t g') stl2 p"
          proof(cases "TypedStoSubpref stl2 pParent pParentT")
            case t2:True
            then show ?thesis using comp
              by (metis CompStoType_sameLoc_sameType stackvalue.inject(4) True cc1 cc2 typedStoSub_imps_negInv)
          next
            case False
            then have "CompStoType tp2 pParentT stl2 pParent" using comp
              by (simp add: cc2)
            then show ?thesis
              using True cc1 by auto
          qed
          then show ?thesis by (simp add: pToStl2)
        next
          case False
          then have cmp:" CompStoType pParentT (STMap t g') pParent p" using prnt by simp
          then have tsp:"TypedStoSubpref p pParent pParentT" using CompStoType_imps_TypedStoSubpref by simp
          then show ?thesis
          proof(cases "TypedStoSubpref stl2 pParent pParentT")
            case True
            then have prntStl2:" CompStoType pParentT tp2 pParent stl2" using comp by simp
            have "CompStoType tp2 (STMap t g') stl2 p " using pToStl2 prntStl2 CompStoType_sharedSub cmp by simp
            then show ?thesis using pToStl2 by simp
          next
            case f1:False
            then show ?thesis
            proof(cases "TypedStoSubpref pParent stl2 tp2")
              case True
              then have "CompStoType tp2 pParentT stl2 pParent" using comp f1 by simp
              then have "CompStoType tp2 (STMap t g') stl2 p" using cmp CompStoType_trns[of tp2 ] by blast
              then show ?thesis using pToStl2 by simp
            next
              case False
              then have "\<not>TypedStoSubpref p stl2 tp2" using f1 cmp tsp NotRelatedPrnt_imps_notRelatedChild[of stl2 pParent pParentT tp2 p] by simp
              then show ?thesis using f1 pToStl2 cmp by simp
            qed
          qed
        qed
      next
        case f1:False
        then show ?thesis
        proof(cases " TypedStoSubpref stl2 p (STMap t g')")
          case stl2ToP:True
          have " CompStoType (STMap t g') tp2 p stl2"
          proof(cases "pParentT = (STMap t g')")
            case True
            then have cc1:"KStoptr p = KStoptr pParent " using prnt
              using comp_stotype_same_type_same_loc by blast
            then have cc2:"TypedStoSubpref stl2 pParent (STMap t g')" using stl2ToP by auto
            then have " CompStoType (STMap t g') tp2 p stl2"
            proof(cases "TypedStoSubpref stl2 pParent pParentT")
              case t2:True
              then have "CompStoType pParentT tp2 pParent stl2" using comp by simp
              then have "CompStoType (STMap t g') tp2 p stl2" using cc1 True by blast
              then show ?thesis by blast
            next
              case False
              then show ?thesis
              proof(cases "TypedStoSubpref pParent stl2 tp2")
                case True
                then have "CompStoType tp2 pParentT stl2 pParent" using comp False by simp
                then show ?thesis using True cc1 f1 by auto
              next
                case f2:False
                then show ?thesis using False True cc2 by blast
              qed
            qed
            then show ?thesis by blast
          next
            case False
            then have cmp:" CompStoType pParentT (STMap t g') pParent p" using prnt by simp
            then have tsp:"TypedStoSubpref p pParent pParentT" using CompStoType_imps_TypedStoSubpref by simp
            then show ?thesis
            proof(cases "TypedStoSubpref stl2 pParent pParentT")
              case True
              then have prntStl2:" CompStoType pParentT tp2 pParent stl2" using comp by simp
              then show ?thesis using CompStoType_sharedSub[OF prntStl2 stl2ToP cmp] by simp
            next
              case f1:False
              then show ?thesis
              proof(cases "TypedStoSubpref pParent stl2 tp2")
                case True
                then have "CompStoType tp2 pParentT stl2 pParent" using comp f1 by simp
                then have "CompStoType tp2 (STMap t g') stl2 p" using cmp CompStoType_trns[of tp2 ] by blast
                then show ?thesis
                  using CompStoType_sameLocNdTyp CompStoType_sharedSub stl2ToP by blast
              next
                case False
                then show ?thesis
                  using NotReachablePrnt_imps_notReachableChild cmp f1 stl2ToP by blast
              qed
            qed
          qed
          then show ?thesis using f1 by (simp )
        next
          case False
          then show ?thesis
            using f1 by auto
        qed
      qed
    next
      case f3:False
      then have StL2:"l2 = Storeloc stl2"
        using in1 by auto

      then have "SCon pParentT pParent (Storage st (Address env))" using pOrigin using 2(1) unfolding TypeSafe_def typeCompat_def by force
      have prnt:" pParentT = (STMap t g') \<and> KStoptr p = KStoptr pParent \<or> extractValueType (KStoptr p) \<noteq> pParent \<and>
          CompStoType pParentT (STMap t g') pParent (extractValueType (KStoptr p))"
        using pOrigin by simp
      then have comp:"(if TypedStoSubpref stl2 pParent pParentT then CompStoType pParentT tp2 pParent stl2
                    else if TypedStoSubpref pParent stl2 tp2 then CompStoType tp2 pParentT stl2 pParent else True)"
        using pParentRelations in1 StL2 prnt by force
      then show ?thesis
      proof(cases "TypedStoSubpref p stl2 tp2")
        case pToStl2:True
        then show ?thesis
        proof(cases "pParentT = (STMap t g')")
          case True
          then have cc1:"KStoptr p = KStoptr pParent " using prnt
            using comp_stotype_same_type_same_loc by blast
          then have cc2:"TypedStoSubpref pParent stl2 tp2" using pToStl2 by auto
          then have "CompStoType tp2 (STMap t g') stl2 p"
          proof(cases "TypedStoSubpref stl2 pParent pParentT")
            case t2:True
            then show ?thesis using comp
              by (metis CompStoType_sameLoc_sameType stackvalue.inject(4) True cc1 cc2 typedStoSub_imps_negInv)
          next
            case False
            then have "CompStoType tp2 pParentT stl2 pParent" using comp
              by (simp add: cc2)
            then show ?thesis
              using True cc1 by auto
          qed
          then show ?thesis by (simp add: pToStl2)
        next
          case False
          then have cmp:" CompStoType pParentT (STMap t g') pParent p" using prnt by simp
          then have tsp:"TypedStoSubpref p pParent pParentT" using CompStoType_imps_TypedStoSubpref by simp
          then show ?thesis
          proof(cases "TypedStoSubpref stl2 pParent pParentT")
            case True
            then have prntStl2:" CompStoType pParentT tp2 pParent stl2" using comp by simp
            have "CompStoType tp2 (STMap t g') stl2 p " using pToStl2 prntStl2 CompStoType_sharedSub cmp by simp
            then show ?thesis using pToStl2 by simp
          next
            case f1:False
            then show ?thesis
            proof(cases "TypedStoSubpref pParent stl2 tp2")
              case True
              then have "CompStoType tp2 pParentT stl2 pParent" using comp f1 by simp
              then have "CompStoType tp2 (STMap t g') stl2 p" using cmp CompStoType_trns[of tp2 ] by blast
              then show ?thesis using pToStl2 by simp
            next
              case False
              then have "\<not>TypedStoSubpref p stl2 tp2" using f1 cmp tsp NotRelatedPrnt_imps_notRelatedChild[of stl2 pParent pParentT tp2 p] by simp
              then show ?thesis using f1 pToStl2 cmp by simp
            qed
          qed
        qed
      next
        case f1:False
        then show ?thesis
        proof(cases " TypedStoSubpref stl2 p (STMap t g')")
          case stl2ToP:True
          have " CompStoType (STMap t g') tp2 p stl2"
          proof(cases "pParentT = (STMap t g')")
            case True
            then have cc1:"KStoptr p = KStoptr pParent " using prnt
              using comp_stotype_same_type_same_loc by blast
            then have cc2:"TypedStoSubpref stl2 pParent (STMap t g')" using stl2ToP by auto
            then have " CompStoType (STMap t g') tp2 p stl2"
            proof(cases "TypedStoSubpref stl2 pParent pParentT")
              case t2:True
              then have "CompStoType pParentT tp2 pParent stl2" using comp by simp
              then have "CompStoType (STMap t g') tp2 p stl2" using cc1 True by blast
              then show ?thesis by blast
            next
              case False
              then show ?thesis
              proof(cases "TypedStoSubpref pParent stl2 tp2")
                case True
                then have "CompStoType tp2 pParentT stl2 pParent" using comp False by simp
                then show ?thesis using True cc1 f1 by auto
              next
                case f2:False
                then show ?thesis using False True cc2 by blast
              qed
            qed
            then show ?thesis by blast
          next
            case False
            then have cmp:" CompStoType pParentT (STMap t g') pParent p" using prnt by simp
            then have tsp:"TypedStoSubpref p pParent pParentT" using CompStoType_imps_TypedStoSubpref by simp
            then show ?thesis
            proof(cases "TypedStoSubpref stl2 pParent pParentT")
              case True
              then have prntStl2:" CompStoType pParentT tp2 pParent stl2" using comp by simp
              then show ?thesis using CompStoType_sharedSub[OF prntStl2 stl2ToP cmp] by simp
            next
              case f1:False
              then show ?thesis
              proof(cases "TypedStoSubpref pParent stl2 tp2")
                case True
                then have "CompStoType tp2 pParentT stl2 pParent" using comp f1 by simp
                then have "CompStoType tp2 (STMap t g') stl2 p" using cmp CompStoType_trns[of tp2 ] by blast
                then show ?thesis
                  using CompStoType_sameLocNdTyp CompStoType_sharedSub stl2ToP by blast
              next
                case False
                then show ?thesis
                  using NotReachablePrnt_imps_notReachableChild cmp f1 stl2ToP by blast
              qed
            qed
          qed
          then show ?thesis using f1 by simp
        next
          case False
          then show ?thesis using f1 by auto
        qed
      qed
    qed
  qed
  have storageSame:"(Storage st' (Address env)) = (Storage st (Address env))" using 16 by simp
  show ?thesis unfolding TypeSafe_def StateInvariant_def
  proof (intros)
    show tcN:"typeCompat (Denvalue env) (Stack st') (Memory st') (Storage st' (Address env)) cd"
      unfolding typeCompat_def
    proof intros
      fix t l' assume a10:"(t, l') |\<in>| fmran (Denvalue env)"
      show "denvalueCon (Stack st') (Memory st') (Storage st' (Address env)) cd t l'"
      proof (split denvalue.split, intros)
        fix loc assume a20:"l' = Stackloc loc"
        show "case accessStore loc (Stack st') of None \<Rightarrow> False
        | Some (KValue val) \<Rightarrow> (case t of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
        | Some (KCDptr stloc) \<Rightarrow> (case t of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
        | Some (KMemptr stloc) \<Rightarrow> (case t of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
        | Some (KStoptr stloc) \<Rightarrow> (case t of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address env)) | _ \<Rightarrow> False)"
        proof (cases "loc = l")

          case False
          show ?thesis
          proof (split option.split, intros)
            assume a30:"accessStore loc (Stack st') = None"
            then have "accessStore loc (Stack st) = None" using 16(4) False by (simp add:stackSingleUpdate)
            then show False using a30 a20 a10 assms TypeSafe_def typeCompat_def False 2(1)
              by (metis option.distinct(1) typeSafeLocExists)
          next
            fix x2 assume a30:"accessStore loc (Stack st') = Some x2"
            then have a40:"accessStore loc (Stack st) = Some x2" using 16(4) False by (simp add:stackSingleUpdate)
            then have a50:"(Memory st) = (Memory st')" using 16(4) by simp
            then have a60:"(Storage st) = (Storage st')" using 16(4) by simp
            show "case x2 of KValue val \<Rightarrow> (case t of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False )
                | KCDptr stloc \<Rightarrow> (case t of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
                | KMemptr stloc \<Rightarrow> (case t of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
                | KStoptr stloc \<Rightarrow> (case t of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address env)) | _ \<Rightarrow> False)"
              using a10 a20 a30 a40 a50 a60 2(1) unfolding TypeSafe_def typeCompat_def by (cases x2; cases t; force)
          qed
        next
          case sameLoc:True
          show ?thesis
          proof (split option.split, intros)
            assume a30:"accessStore loc (Stack st') = None"
            then show False using a20 a10 assms(1) sameLoc 16(4) notNoneUpdate by simp
          next
            fix x2 assume a30:"accessStore loc (Stack st') = Some x2"
            then have x2IsP:"x2 = KStoptr p" using 16 sameLoc by auto
            show "case x2 of KValue val \<Rightarrow> (case t of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
            | KCDptr stloc \<Rightarrow> (case t of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
            | KMemptr stloc \<Rightarrow> (case t of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
            | KStoptr stloc \<Rightarrow> (case t of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address env)) | _ \<Rightarrow> False)"
            proof(cases "x2")
              case (KValue x1)
              then show ?thesis using x2IsP by auto
            next
              case (KCDptr x2)
              then show ?thesis using x2IsP by (simp add:sameLoc)
            next
              case (KMemptr x3)
              then show ?thesis using x2IsP by (simp add:sameLoc)
            next
              case (KStoptr x4)
              then show ?thesis using x2IsP a10 a20 lDen storageSame sameLoc
                using pSCon by force
            qed
          qed
        qed
      next
        fix x2 assume a20:"l' = Storeloc x2"
        then have "(Storage st' (Address env)) = (Storage st (Address env))" using 16(4) by simp
        then show "case t of type.Storage typ \<Rightarrow> SCon typ x2 (Storage st' (Address env)) | _ \<Rightarrow> False" using a10 a20 TypeSafe_def 2(1) pSCon a10 a20 lDen storageSame
        proof -
          have "\<And>t d. (t, d) |\<notin>| fmran (Denvalue env) \<or>
                  (case d of Stackloc l \<Rightarrow> (case accessStore l (Stack st) of None \<Rightarrow> False
                  | Some (KValue l) \<Rightarrow> (case t of Value t \<Rightarrow> typeCon t l | _ \<Rightarrow> False )
                  | Some (KCDptr l) \<Rightarrow> (case t of Calldata m \<Rightarrow> MCon m cd l | _ \<Rightarrow> False )
                  | Some (KMemptr l) \<Rightarrow> (case t of type.Memory m \<Rightarrow> MCon m (Memory st) l | _ \<Rightarrow> False )
                  | Some (KStoptr l) \<Rightarrow> (case t of type.Storage s \<Rightarrow> SCon s l (Storage st (Address env)) | _ \<Rightarrow> False))
                  | Storeloc l \<Rightarrow> (case t of type.Storage s \<Rightarrow> SCon s l (Storage st (Address env)) | _ \<Rightarrow> False))"
            using 2(1) unfolding TypeSafe_def typeCompat_def by auto
          then show ?thesis
            by (metis (no_types) denvalue.simps(6) a10 a20 storageSame)
        qed
      qed
    qed
    have "typeCompat (Denvalue env) (Stack st) (Memory st') (Storage st' (Address env)) cd"
      unfolding typeCompat_def
    proof intros
      fix t l' assume a10:"(t, l') |\<in>| fmran (Denvalue env)"
      show "denvalueCon (Stack st) (Memory st') (Storage st' (Address env)) cd t l'"
      proof(cases "l'")
        case (Stackloc x1)
        then show ?thesis
        proof(cases "x1 = l")
          case sameLoc:True
          then show ?thesis
          proof(cases "accessStore x1 (Stack st)")
            case None
            then show ?thesis using Stackloc a10 assms(1) sameLoc 16(4)
              by (metis 2(1) option.distinct(1) typeSafeAllStacklocsExist)
          next
            case (Some a)
            then obtain t''' where "t = type.Storage t'''" using lDen a10 Stackloc 2(1) sameLoc by blast
            then have x2IsP:"\<exists>p. a = KStoptr p" using 16 sameLoc 2(1) a10 Stackloc Some unfolding TypeSafe_def typeCompat_def
              by (cases a, force,simp,fastforce+)
            then show ?thesis using x2IsP a10 Stackloc lDen storageSame sameLoc Some 2(1) unfolding TypeSafe_def typeCompat_def
              using pSCon by force
          qed
        next
          case False
          then have "accessStore x1 (Stack st) = accessStore x1 (Stack st')"
            using stackChanged by auto
          then show ?thesis using a10 Stackloc tcN unfolding typeCompat_def by force
        qed
      next
        case (Storeloc x2)
        then show ?thesis using a10 tcN unfolding typeCompat_def by force
      qed
    qed
  next
    show "unique_locations (Denvalue env)" using 2(1) typeSafeUnique by auto
  next
    have "(Accounts st) = Accounts(st')" using 16 by simp
    then show "balanceTypes (Accounts st')" using balanceTypes_def balanceTypes_def 2(1) typeSafeAccounts by simp
  next
    have a0:"compPointers (Stack st) (Denvalue env)" using 2(1) storageSame unfolding TypeSafe_def by simp
    show " compPointers (Stack st') (Denvalue env)" unfolding compPointers_def
    proof(intros)
      fix tp1 tp2 l1 l22 l1' l2' stl1 stl2
      assume a1:"(type.Storage tp1, l1) |\<in>| fmran (Denvalue env) \<and>
   (type.Storage tp2, l22) |\<in>| fmran (Denvalue env) \<and>
   (l1 = Stackloc l1' \<and> accessStore l1' (Stack st') = Some (KStoptr stl1) \<or> l1 = Storeloc stl1) \<and>
   (l22 = Stackloc l2' \<and> accessStore l2' (Stack st') = Some (KStoptr stl2) \<or> l22 = Storeloc stl2)"
      have a2:"(\<forall>x y. x |\<in>| fmran (Denvalue env) \<and> y |\<in>| fmran (Denvalue env) \<and> snd x = snd y \<longrightarrow> x = y)"
        using 2(1) unfolding TypeSafe_def unique_locations_def by simp

      then show "if TypedStoSubpref stl2 stl1 tp1 then CompStoType tp1 tp2 stl1 stl2 else if TypedStoSubpref stl1 stl2 tp2 then CompStoType tp2 tp1 stl2 stl1 else True"
      proof(cases "l1 = Storeloc stl1")
        case t1:True
        then show ?thesis
        proof(cases "l22 = Storeloc stl2")
          case True
          then show ?thesis using t1 a0 a1 unfolding compPointers_def by blast
        next
          case False
          then have a4:"l22 = Stackloc l2' \<and> accessStore l2' (Stack st') = Some (KStoptr stl2)" using a1 by simp
          then show ?thesis
          proof(cases "l2' = l")
            case True
            then have "stl2 = p" using a4 16 by simp
            then show ?thesis using pRelations a1 a0 t1 True a4 lDen by blast
          next
            case False
            then have " accessStore l2' (Stack st') = accessStore l2' (Stack st)" using stackChanged a4 by simp
            then show ?thesis using a0 a1 t1 unfolding compPointers_def by metis
          qed
        qed
      next
        case f1:False
        then have a4:"l1 = Stackloc l1' \<and> accessStore l1' (Stack st') = Some (KStoptr stl1)" using a1 by simp
        then show ?thesis
        proof(cases "l22 = Storeloc stl2")
          case t1:True
          then show ?thesis
          proof(cases "l1' = l")
            case True
            then have "stl1 = p" using a4 16 by simp
            then show ?thesis using pRelations a1 a0 t1 True a4 lDen
              by (metis CompStoType_sameLoc_sameType type.inject(4) typedStoSub_imps_negInv)
          next
            case False
            then have " accessStore l1' (Stack st') = accessStore l1' (Stack st)" using stackChanged a4 by simp
            then show ?thesis using a0 a1 t1 unfolding compPointers_def by metis
          qed
        next
          case False
          then have a4':"l22 = Stackloc l2' \<and> accessStore l2' (Stack st') = Some (KStoptr stl2)" using a1 by simp
          then show ?thesis
          proof(cases "l1' = l")
            case True
            then have p1:"stl1 = p" using a4 16 by simp
            then have tp1c:"tp1 = (STMap t g')" using lDen a1
              using True a4 by auto
            then show ?thesis
            proof(cases "l2' = l")
              case True
              then have p2:"stl2 = p" using a4' 16 by auto
              then have tp2c:"tp2 = (STMap t g')" using lDen a1 True a4' by auto
              then show ?thesis using p2 p1 tp1c tp2c by auto
            next
              case False
              then have " accessStore l2' (Stack st') = accessStore l2' (Stack st)" using stackChanged a4 by simp
              then show ?thesis
                by (metis CompStoType_sameLoc_sameType a1 p1 pRelations tp1c typedStoSub_imps_negInv)
            qed
          next
            case False
            then have same1:" accessStore l1' (Stack st') = accessStore l1' (Stack st)" using stackChanged a4 by simp
            then show ?thesis
            proof(cases "l2' = l")
              case True
              then have p2:"stl2 = p" using a4' 16 by auto
              then have tp2c:"tp2 = (STMap t g')" using lDen a1 True a4' by auto
              then show ?thesis using same1 pRelations p2 tp2c a1
                by metis
            next
              case False
              then have " accessStore l2' (Stack st') = accessStore l2' (Stack st)" using stackChanged a4 by simp
              then show ?thesis using a1 a0 same1
                using compPointers_def by auto
            qed
          qed
        qed
      qed
    qed
  next
    show "svalueTypes (Svalue env)" using svalueTypes_def typeSafeSvalue 2(1) by simp
  next
    have "(Storage st') = (Storage st)" using 16(4) by simp
    then show "safeContract (Accounts st') (Storage st')" using 2(1) 16 unfolding safeContract_def TypeSafe_def by auto
  next
    have a10:"Toploc (Stack st') = Toploc (Stack st)" using 16(4) unfolding updateStore_def by simp
    then have a20:"\<exists>val. accessStore l (Stack st) = Some val" using t'InDen typeSafeLocExists 2(1) TypeSafe_def by blast
    then have a30:"(\<forall>tloc loc. Toploc (Stack st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Stack st) = None)
                 \<and>(\<forall>loc y. accessStore loc (Stack st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Stack st). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))"
      using 2(1) unfolding TypeSafe_def lessThanTopLocs_def by simp
    then have a40:"(\<forall>tloc loc. Toploc (Stack st') \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Stack st) = None)
                  \<and>(\<forall>loc y. accessStore loc (Stack st) = Some y \<longrightarrow> (\<exists>tloc<Toploc (Stack st'). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)))"
      using a10 by simp
    show "lessThanTopLocs (Stack st')" unfolding lessThanTopLocs_def
    proof intros
      fix tloc loc
      assume *:"Toploc (Stack st') \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
      then show "accessStore loc (Stack st') = None"
      proof(cases "loc = l")
        case True
        then show ?thesis using * a10
          by (metis a20 a30 option.distinct(1))
      next
        case False
        then have a50:"accessStore loc (Stack st) = accessStore loc (Stack st')" using 16(4) unfolding updateStore_def accessStore_def by simp
        then show ?thesis using 2(1) a40 * a10 False a30 by simp
      qed
    next
      fix loc y
      assume *:" accessStore loc (Stack st') = Some y "
      show "\<exists>tloc<Toploc (Stack st'). LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc)"
      proof(cases "loc = l")
        case True
        then show ?thesis using *a10 a20 a30 by simp
      next
        case False
        then have a50:"accessStore loc (Stack st) = accessStore loc (Stack st')" using 16(4) unfolding updateStore_def accessStore_def by simp
        then show ?thesis using * 2(1) a40 by simp
      qed
    qed
  next
    show "lessThanTopLocs cd" using 2(1) unfolding TypeSafe_def using 16 by auto
  next
    show "lessThanTopLocs (Memory st')" using 2(1) unfolding TypeSafe_def using 16 by auto
  next
    have "envAddressesWellFormed env" using 2(1) unfolding TypeSafe_def by auto
    then show "addressFormat (Address env)" and "addressFormat (Sender env)" by simp+
  next
    show "AddressTypes (Accounts st')" using 2(1) unfolding TypeSafe_def using 16 by simp
  next
    have accSame:"Accounts st'= Accounts st" using 16 by auto
    from 2(3) obtain c_fi ct_fi dud_fi where fi:"
         Type (Accounts st (Address env)) = Some (atype.Contract c_fi) \<and>
         Contract env = c_fi \<and>
         ep $$ c_fi = Some (ct_fi, dud_fi) \<and>
         (\<forall>id v. (ct_fi $$ id = Some (Var v)) = (Denvalue env $$ id = Some (type.Storage v, Storeloc id))) \<and>
         (\<forall>id v loc. Denvalue env $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc) \<and>
         (\<forall>t0 l0 p0.
             (type.Storage t0, Stackloc l0) |\<in>| fmran (Denvalue env) \<and> accessStore l0 (Stack st) = Some (KStoptr p0) \<longrightarrow>
             (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue env) \<and> CompStoType t' t0 l' p0))"
      unfolding fullyInitialised_def by blast
    have fiPtrs':"\<forall>t''' l''' p'''.
             (type.Storage t''', Stackloc l''') |\<in>| fmran (Denvalue env) \<and> accessStore l''' (Stack st') = Some (KStoptr p''') \<longrightarrow>
             (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue env) \<and> CompStoType t' t''' l' p''')"
    proof (intro allI impI)
      fix t''' l''' p'''
      assume in1:"(type.Storage t''', Stackloc l''') |\<in>| fmran (Denvalue env)\<and>accessStore l''' (Stack st') = Some (KStoptr p''') "
      show "\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue env) \<and> CompStoType t' t''' l' p'''"
      proof(cases "l''' = l")
        case True
        then have "p''' = p" using 16 in1 unfolding accessStore_def updateStore_def by simp
        then show ?thesis using pOrigin
          by (metis CompStoType_sameLocNdTyp True type.inject(4) in1 lDen extractValueType.simps(4))
      next
        case False
        then have "accessStore l''' (Stack st') = accessStore l''' (Stack st)"
          using stackChanged by force
        then show ?thesis using fi in1
          by presburger
      qed
    qed
    show "fullyInitialised env (Accounts st') (Stack st')"
      unfolding fullyInitialised_def using fi fiPtrs' accSame by metis
  next
    have cc0:"\<forall>l ptr_loc. accessStore l (Stack st') = Some (KMemptr ptr_loc) \<longrightarrow> accessStore l (Stack st) = Some (KMemptr ptr_loc)"
      using 16(4) unfolding updateStore_def accessStore_def by auto
    show "denvalueTypeCorrectness env (Stack st') (Memory st')"

      unfolding denvalueTypeCorrectness_def
    proof intros
      fix t l ptr_loc sub_loc
      assume "(type.Memory t, Stackloc l) |\<in>| fmran (Denvalue env) \<and>
     accessStore l (Stack st') = Some (KMemptr ptr_loc)"
      then have "(case t of
       MTArray len arr \<Rightarrow>
         (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr)
       | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st) = Some (MTValue val))"
        using 2(1) unfolding TypeSafe_def denvalueTypeCorrectness_def using cc0 by blast
      moreover have "Memory st = Memory st'" using 16(4) by simp
      ultimately show "case t of
     MTArray len arr \<Rightarrow>
       (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr)
     | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st') = Some (MTValue val)"
        by metis
    qed
  next
    show "subPrefixStructuralConsistency (Memory st')" using 2(1) unfolding TypeSafe_def using 16(4) by simp
  next
    show "SomeValSomeTyp (Memory st')" using 2(1) unfolding TypeSafe_def using 16(4) by simp
  next
    show "\<And>locs t. accessTypeStore locs (Memory st) = Some t \<Longrightarrow> accessTypeStore locs (Memory st') = Some t"
      using 2(1) unfolding TypeSafe_def using 16(4) by simp
  next
    show "\<And>locs v. accessStore locs (Memory st) = Some (MPointer v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MPointer v')"
      using 16(4) by simp
  next
    show "\<And>locs v. accessStore locs (Memory st) = Some (MValue v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MValue v')"
      using 16(4) by simp
  next
    show " \<And>i loc. i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<Longrightarrow> accessStore loc
        (Memory st) = None \<Longrightarrow> accessStore loc (Memory st') = None"
      using 16(4) by simp
  next
    show "Toploc (Memory st) \<le> Toploc (Memory st')" using 16(4) by simp
  qed
qed

end

end
