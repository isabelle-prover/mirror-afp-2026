section \<open>Supporting lemmas for statement preservation\<close>

theory TypeSafe_Statement_Support
  imports TypeSafe_Expressions
begin

context typesafe_base
begin

subsection \<open>Stack updates and value conversion\<close>

lemma diffTypeDiffLoc:
  assumes "st' = st\<lparr>Stack := updateStore l v (Stack st), Gas:=g\<rparr>"
    and "v' \<noteq> v"
    and "accessStore l1 (Stack st') = Some v'"
  shows "l1 \<noteq> l" using assms notNoneUpdate by fastforce

lemma stackSingleUpdate:
  assumes "st' = st\<lparr>Stack := updateStore l v (Stack st), Gas:=g\<rparr>"
  shows "\<forall>nl \<noteq>l. accessStore nl (Stack st) = accessStore nl (Stack st')"
proof (intros)
  fix nl
  assume a1:"nl \<noteq> l"
  then have "accessStore nl (updateStore l v (Stack st)) = accessStore nl (Stack st)"
    unfolding updateStore_def by (simp add: accessStore_def)
  then show "accessStore nl (Stack st) = accessStore nl (Stack st')" using assms by simp
qed

lemma updateOneType:
  assumes "st' = st\<lparr>Stack := updateStore l v (Stack st), Gas:=g\<rparr>"
    and "v' \<noteq> v"
  shows "accessStore l1 (Stack st') = Some v' \<Longrightarrow> accessStore l1 (Stack st) = Some v'"
proof -
  assume a1:"accessStore l1 (Stack st') = Some v'"
  then have "l1 \<noteq> l" using diffTypeDiffLoc[of st' g l v st v' l1] assms by simp
  then show "accessStore l1 (Stack st) = Some v'" using stackSingleUpdate[of st' g l v st] assms a1 by simp
qed


lemma typeSafeLocExists:
  assumes "TypeSafe ev (Accounts st) (Stack st) (Memory st) (Storage st) cd"
    and "(t, l) |\<in>| fmran (Denvalue ev)"
    and "l = Stackloc loc"
    and "unique_locations (Denvalue ev)"
    and "balanceTypes (Accounts st)"
  shows "\<exists>val. accessStore loc (Stack st) = Some(val)"
proof -
  have a10:"TypeSafe ev (Accounts st) (Stack st) (Memory st) (Storage st) cd = (unique_locations (Denvalue ev) \<and>
     balanceTypes (Accounts st) \<and>
     (\<forall>t l. (t, l) |\<in>| fmran (Denvalue ev) \<longrightarrow>
            (denvalueCon (Stack st) (Memory st) (Storage st (Address ev)) cd t l)))"
    using assms TypeSafe_def typeCompat_def by simp
  then show ?thesis
  proof(cases "accessStore loc (Stack st)")
    case None
    then have "False" using a10 assms by force
    then show ?thesis by simp
  next
    case (Some a)
    then show ?thesis using a10 assms by simp
  qed
qed

lemma typeConConvert:
  assumes "local.expr ex env cd (st) g' = Normal ((KValue v, Value t2), g)"
    and "TypeSafe env (Accounts st) (Stack st) (Memory st) (Storage st) cd"
    and "convert t2 t' v = Some (v)"
    and "fullyInitialised env (Accounts st) (Stack st)"
  shows "typeCon t' v"
proof -
  have "Memory (st) = Memory st" by simp
  moreover have "Storage (st) = Storage st" by simp
  moreover have "Accounts (st) = Accounts st" by simp
  moreover have "Stack st = Stack (st)" by simp
  ultimately have "TypeSafe env (Accounts st) (Stack st) (Memory st) (Storage st) cd" using assms(2) by metis
  then have a10:"typeCon t2 v" using exprTypeconInduct(3) assms(1,4) by force
  then show "typeCon t' v" using a10 assms(3) typeSafeConvert by simp
qed


subsection \<open>Locations returned by left-hand expressions\<close>

text \<open>If storage is @{const SCon} and @{const lexp} returns a location in it, the types agree.\<close>

lemma lexpStorage:
  assumes "TypeSafe env (Accounts st) (Stack st) (Memory st) (Storage st) cd"
    and "lexp lv env cd (st\<lparr>Gas := g\<rparr>) g = Normal ((LStoreloc locChanged, type.Storage (STValue t')),g')"
    and "fullyInitialised env (Accounts st) (Stack st)"

obtains (1)
  "((type.Storage (STValue t'), Storeloc locChanged) |\<in>| fmran (Denvalue env))"
| (2) l t
where "((type.Storage t, Storeloc l) |\<in>| fmran (Denvalue env))"
  and "(TypedStoSubpref locChanged l t \<and> CompStoType t (STValue t') l locChanged)"

| (3) l' t l
where "((type.Storage t, Stackloc l) |\<in>| fmran (Denvalue env))"
  and "accessStore l (Stack st) = Some (KStoptr l')"
  and "(TypedStoSubpref locChanged l' t \<and> CompStoType t (STValue t') l' locChanged)"
proof (cases lv)
  case (Id x1)
  then have "lexp (Id x1) env cd (st\<lparr>Gas := g\<rparr>) g = Normal ((LStoreloc locChanged, type.Storage (STValue t')), g')" using assms(2) by simp
  then have "Denvalue env $$ x1 = Some (type.Storage (STValue t'), Storeloc locChanged) "
    using Id lexp.simps(1)[of x1 env cd "(st\<lparr>Gas := g\<rparr>)" g] by (auto split:option.splits denvalue.splits)
  then show ?thesis by (simp add: "1" fmranI)
next
  case (Ref x21 x22)
  then have *: "lexp (Ref x21 x22) env cd (st\<lparr>Gas := g\<rparr>) g = Normal ((LStoreloc locChanged, type.Storage (STValue t')), g')" using assms(2) by simp
  then show ?thesis
  proof(cases "Denvalue env $$ x21")
    case None
    then show ?thesis using * lexp.simps(2) Ref by simp
  next
    case (Some a)
    then obtain tp loc where adef:"a = (type.Storage tp, loc)" using * lexp.simps(2) Ref by (cases a; (auto split: result.splits type.splits denvalue.splits option.splits stackvalue.splits))
    then have b6:"(type.Storage tp, loc) |\<in>| fmran (Denvalue env)" using Some by (simp add: fmranI)

    then show ?thesis
    proof(cases loc)
      case (Stackloc x1)
      then show ?thesis
      proof(cases "accessStore x1 (Stack st)")
        case None
        then show ?thesis using * Ref Stackloc lexp.simps(2)[of x21 x22 env cd "(st\<lparr>Gas := g\<rparr>)" g] Some adef by simp
      next
        case some2:(Some a)
        then obtain x4 where x4def:"a = KStoptr x4" using * Ref Stackloc lexp.simps(2)[of x21 x22 env cd "(st\<lparr>Gas := g\<rparr>)" g] Some adef some2 by (cases a; auto)
        then obtain l'' t'' where b20:"ssel tp x4 x22 env cd (st\<lparr>Gas := g\<rparr>) g = Normal ((l'', t''), g')"
          using Stackloc Some Ref * lexp.simps(2) adef some2 by (auto split: result.splits type.splits)
        have b10:"SCon tp x4 (Storage st (Address env))" using assms b6 some2 Stackloc x4def unfolding TypeSafe_def typeCompat_def by fastforce
        then have b30:"locChanged = l'' \<and> (STValue t') = t''" using * lexp.simps(2) Ref adef Stackloc b20 some2 x4def Some Ref b6 by simp

        then show ?thesis
        proof(cases x22)
          case Nil
          then have b25:"tp = t'' \<and> x4 = l''" using b20 ssel.simps(1) by simp
          then have b30:"locChanged = l'' \<and> (STValue t') = t''" using * lexp.simps(2) Ref adef Stackloc some2 x4def b20 Some Ref b6 by simp
          then show ?thesis using b6 3 b25 Stackloc some2 x4def by auto
        next
          case (Cons a list)
          then have b10:"(CompStoType tp t'' x4 l'')"
            using exprTypeconInduct(2)[of tp x4 x22 env cd "(st\<lparr>Gas := g\<rparr>)" g l'' t'' g'] assms
            using b10 b20 some2 x4def unfolding fullyInitialised_def by simp
          have b30:"l'' = locChanged \<and> (STValue t') = t''" using * lexp.simps(2) Ref adef Stackloc some2 x4def b20 Some Ref b6 by simp
          then have "CompStoType tp (STValue t') x4 l''" using b10 by simp
          then show ?thesis using * lexp.simps(2) Ref adef Stackloc some2 x4def b20 Some Ref b6 b10 b30 3
            using CompStoType_imps_TypedStoSubpref by blast
        qed
      qed
    next
      case (Storeloc x2)
      then have b10:"SCon tp x2 (Storage st (Address env))" using assms b6 unfolding TypeSafe_def typeCompat_def by force
      then obtain l'' t'' where b20:"ssel tp x2 x22 env cd (st\<lparr>Gas := g\<rparr>) g = Normal ((l'', t''), g')"
        using Storeloc Some Ref * lexp.simps(2) adef by (auto split: result.splits type.splits)
      then show ?thesis
      proof(cases x22)
        case Nil
        then have b25:"tp = t'' \<and> x2 = l''" using b20 ssel.simps(1) by simp
        then have b30:"locChanged = l'' \<and> (STValue t') = t''" using * lexp.simps(2) Ref adef Storeloc b20 Some Ref b6 by simp
        then show ?thesis using b6 1 adef Some Ref * b25 b20 by (simp add: Storeloc)
      next
        case (Cons a list)
        then have b10:"CompStoType tp t'' x2 l''"
          using exprTypeconInduct(2)[of tp x2 x22 env cd "(st\<lparr>Gas := g\<rparr>)" g l'' t'' g'] assms
          using b10 b20 Storeloc unfolding fullyInitialised_def by simp
        have b30:"l'' = locChanged \<and> (STValue t') = t''" using * lexp.simps(2) Ref adef Storeloc b20 Some Ref b6 by simp
        then have "CompStoType tp (STValue t') x2 l''" using b10 by simp
        then show ?thesis using b30 b6 2 adef Some Ref * b10 b20 Storeloc
          using CompStoType_imps_TypedStoSubpref by blast
      qed
    qed
  qed
qed

subsection \<open>Storage variables of fully initialised environments\<close>

lemma typeSafe_storeloc_scon_from_denvalue:
  assumes ts: "TypeSafe env acc sk mem sto cd"
    and inDen: "(type.Storage tp, Storeloc i) |\<in>| fmran (Denvalue env)"
  shows "SCon tp i (sto (Address env))"
  using sameStoLocTSafe[OF ts] inDen by blast

lemma fi_contract_var_to_denvalue_storeloc:
  assumes fi: "fullyInitialised env acc sk"
    and addrEq: "Address e = Address env"
    and typedE: "Type (acc (Address e)) = Some (atype.Contract (Contract e))"
    and epLookup: "ep $$ Contract e = Some (ct, dud)"
    and ctVar: "ct $$ i = Some (Var tp)"
  shows "Denvalue env $$ i = Some (type.Storage tp, Storeloc i)"
proof -
  obtain c ct_fi dud_fi where
      fiType: "Type (acc (Address env)) = Some (atype.Contract c)"
    and fiCon: "Contract env = c"
    and fiEp: "ep $$ c = Some (ct_fi, dud_fi)"
    and fiMap: "(\<forall>id v. (ct_fi $$ id = Some (Var v)) = (Denvalue env $$ id = Some (type.Storage v, Storeloc id)))"
    and fiLoc: "(\<forall>id v loc. Denvalue env $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc)"
    and fiPtr: "(\<forall>t l p.
              (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue env) \<and> accessStore l sk = Some (KStoptr p) \<longrightarrow>
              (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue env) \<and> CompStoType t' t l' p))"
    using fi unfolding fullyInitialised_def by blast
  have cEq: "Contract e = Contract env"
  proof -
    have "Type (acc (Address env)) = Some (atype.Contract (Contract e))"
      using typedE addrEq by simp
    moreover have "Type (acc (Address env)) = Some (atype.Contract (Contract env))"
      using fiType fiCon by simp
    ultimately show ?thesis by simp
  qed
  have epEnv: "ep $$ Contract env = Some (ct, dud)"
    using epLookup cEq by simp
  have epEnvFi: "ep $$ Contract env = Some (ct_fi, dud_fi)"
    using fiEp fiCon by simp
  have ctEq: "ct = ct_fi"
    using epEnv epEnvFi by auto
  have "ct_fi $$ i = Some (Var tp)"
    using ctVar ctEq by simp
  then show ?thesis
    using fiMap by blast
qed

lemma fiPtr_parent_from_fullyInitialised:
  assumes fi: "fullyInitialised env acc sk"
    and inDen: "(type.Storage t, Stackloc l) |\<in>| fmran (Denvalue env)"
    and ptr: "accessStore l sk = Some (KStoptr p)"
  shows "\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue env) \<and> CompStoType t' t l' p"
  using fi inDen ptr unfolding fullyInitialised_def by blast

lemma fi_denvalue_storeloc_to_contract_var:
  assumes fi: "fullyInitialised env acc sk"
    and epLookup: "ep $$ Contract env = Some (ct, dud)"
    and inDen: "(type.Storage tp, Storeloc i) |\<in>| fmran (Denvalue env)"
  shows "ct $$ i = Some (Var tp)"
proof -
  obtain c ct_fi dud_fi where
      fiType: "Type (acc (Address env)) = Some (atype.Contract c)"
    and fiCon: "Contract env = c"
    and fiEp: "ep $$ c = Some (ct_fi, dud_fi)"
    and fiMap: "(\<forall>id v. (ct_fi $$ id = Some (Var v)) = (Denvalue env $$ id = Some (type.Storage v, Storeloc id)))"
    and fiLoc: "(\<forall>id v loc. Denvalue env $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc)"
    and fiPtr: "(\<forall>t l p.
              (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue env) \<and> accessStore l sk = Some (KStoptr p) \<longrightarrow>
              (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue env) \<and> CompStoType t' t l' p))"
    using fi unfolding fullyInitialised_def by blast
  have epEnvFi: "ep $$ Contract env = Some (ct_fi, dud_fi)"
    using fiEp fiCon by simp
  have ctEq: "ct = ct_fi"
    using epLookup epEnvFi by auto
  obtain id where idDef: "Denvalue env $$ id = Some (type.Storage tp, Storeloc i)"
    using inDen by blast
  then have "id = i" using fiLoc by blast
  then have denI: "Denvalue env $$ i = Some (type.Storage tp, Storeloc i)"
    using idDef by simp
  then have "ct_fi $$ i = Some (Var tp)"
    using fiMap by blast
  then show ?thesis using ctEq by simp
qed

lemma safeContract_field_scon_from_typeCompat:
  assumes ts: "TypeSafe env acc sk mem sto cd"
    and fi: "fullyInitialised env acc sk"
    and addrEq: "Address e = Address env"
    and typedE: "Type (acc (Address e)) = Some (atype.Contract (Contract e))"
    and epLookup: "ep $$ Contract e = Some (ct, dud)"
    and ctVar: "ct $$ i = Some (Var tp)"
  shows "SCon tp i (sto (Address env))"
proof -
  have denLookup: "Denvalue env $$ i = Some (type.Storage tp, Storeloc i)"
    using fi_contract_var_to_denvalue_storeloc[OF fi addrEq typedE epLookup ctVar] .
  have inDen: "(type.Storage tp, Storeloc i) |\<in>| fmran (Denvalue env)"
    using denLookup by (simp add: fmranI)
  show ?thesis
    using typeSafe_storeloc_scon_from_denvalue[OF ts inDen] .
qed

lemma safeContract_other_address_preserved:
  assumes sc: "safeContract acc sto"
    and stoEq: "\<forall>a. a \<noteq> a0 \<longrightarrow> sto' a = sto a"
    and addNe: "Address e \<noteq> a0"
    and typedE: "Type (acc (Address (e::environment))) = Some (atype.Contract (Contract e))"
    and epLookup: "ep $$ Contract e = Some (ct, dud)"
    and ctVar: "ct $$ i = Some (Var tp)"
  shows "SCon tp i (sto' (Address e))"
proof -
  have "SCon tp i (sto (Address e))"
    using sc typedE epLookup ctVar unfolding safeContract_def by blast
  moreover have "sto' (Address e) = sto (Address e)"
    using stoEq addNe by blast
  ultimately show ?thesis by simp
qed

lemma copy_dest_scon_from_rel:
  assumes copyStep: "copy p l x t (Storage st (Address env)) = Some s"
    and tEq: "t' = STArray x t"
    and rootSCon: "SCon (STArray x t) l (Storage st (Address env))"
    and srcSCon: "SCon (STArray x t) p (Storage st (Address env))"
    and denSub: "(if TypedStoSubpref stloc lsrc tsrc then CompStoType tsrc tp'' lsrc stloc
                 else if TypedStoSubpref lsrc stloc tp'' then CompStoType tp'' tsrc stloc lsrc else True)"
    and paInf: "(tp'' = (STArray x t) \<and> KStoptr p = KStoptr stloc
                \<or> extractValueType (KStoptr p) \<noteq> stloc \<and> CompStoType tp'' (STArray x t) stloc (extractValueType (KStoptr p)))"
    and rel: "CompStoType tsrc (STArray x t) lsrc l"
  shows "SCon (STArray x t) l s"
proof (cases "p = l")
  case pIsL: True
  then show ?thesis
    using copy_same_SCon copyStep tEq rootSCon by (metis copy_def)
next
  case pNotl: False
  then show ?thesis
  proof (cases "p = stloc")
    case True
    then have j1:"(if TypedStoSubpref p lsrc tsrc then CompStoType tsrc (STArray x t) lsrc p
                   else if TypedStoSubpref lsrc p (STArray x t) then CompStoType (STArray x t) tsrc p lsrc else True)"
      using denSub paInf by fastforce
    then have j2:"\<not>TypedStoSubpref p l (STArray x t) \<and> \<not>TypedStoSubpref l p (STArray x t)"
      using comp_stotype_same_type_same_loc j1 pNotl rel
      by (metis CompStoType_imps_TypedStoSubpref CompStoType_same_type_same_depth CompStoType_trns NotReachablePrnt_imps_notReachableChild NotRelatedPrnt_imps_notRelatedChild
          same_depth_imp_neg_TypedStoSubpref)
    moreover have "\<forall>subL. TypedStoSubpref subL l (STArray x t) \<longrightarrow> \<not> TypedStoSubpref subL p (STArray x t)"
      using NotRelatedPrnt_imps_notRelatedChild[of p l "(STArray x t)" "(STArray x t)"] j2 by blast
    moreover have "\<forall>subL. TypedStoSubpref subL p (STArray x t) \<longrightarrow> \<not> TypedStoSubpref subL l (STArray x t)"
      using j2 NotRelatedPrnt_imps_notRelatedChild by blast
    ultimately show ?thesis
      using copy_notSub_SCon copyStep tEq rootSCon srcSCon by (metis (lifting) copy_def)
  next
    case False
    then have j1:"CompStoType tp'' (STArray x t) stloc p" using paInf by simp
    show ?thesis
    proof (cases "TypedStoSubpref stloc lsrc tsrc")
      case True
      then have "CompStoType tsrc tp'' lsrc stloc" using denSub by simp
      then have j5:"CompStoType tsrc (STArray x t) lsrc p"
        using CompStoType_trns j1 False by blast
      have j10:"CompStoType tsrc (STArray x t) lsrc l" using rel .
      then have j20:"lsrc \<noteq> l \<and> lsrc \<noteq> p" using pNotl j5 False
        using CompStoType_sameLoc_sameType comp_stotype_same_type_same_loc by blast
      then have j2:"\<not>TypedStoSubpref p l (STArray x t) \<and> \<not>TypedStoSubpref l p (STArray x t)"
        using CompStoType_same_type_same_depth j5 j10 pNotl same_depth_imp_neg_TypedStoSubpref by blast
      moreover have "\<forall>subL. TypedStoSubpref subL l (STArray x t) \<longrightarrow> \<not> TypedStoSubpref subL p (STArray x t)"
        using NotRelatedPrnt_imps_notRelatedChild[of p l "(STArray x t)" "(STArray x t)"] j2 by blast
      moreover have "\<forall>subL. TypedStoSubpref subL p (STArray x t) \<longrightarrow> \<not> TypedStoSubpref subL l (STArray x t)"
        using j2 NotRelatedPrnt_imps_notRelatedChild by blast
      ultimately show ?thesis
        using copy_notSub_SCon copyStep tEq rootSCon srcSCon by (metis (lifting) copy_def)
    next
      case f2: False
      then show ?thesis
      proof (cases "TypedStoSubpref lsrc stloc tp''")
        case True
        then have j5:"CompStoType tp'' tsrc stloc lsrc" using denSub f2 by auto
        have j10:"CompStoType tp'' (STArray x t) stloc p" using j1 by simp
        have j11:"CompStoType tp'' (STArray x t) stloc l" using CompStoType_trns j5 rel by blast
        then have j2:"\<not>TypedStoSubpref p l (STArray x t) \<and> \<not>TypedStoSubpref l p (STArray x t)"
          using CompStoType_same_type_same_depth j10 pNotl same_depth_imp_neg_TypedStoSubpref by blast
        moreover have "\<forall>subL. TypedStoSubpref subL l (STArray x t) \<longrightarrow> \<not> TypedStoSubpref subL p (STArray x t)"
          using NotRelatedPrnt_imps_notRelatedChild[of p l "(STArray x t)" "(STArray x t)"] j2 by blast
        moreover have "\<forall>subL. TypedStoSubpref subL p (STArray x t) \<longrightarrow> \<not> TypedStoSubpref subL l (STArray x t)"
          using j2 NotRelatedPrnt_imps_notRelatedChild by blast
        ultimately show ?thesis
          using copy_notSub_SCon copyStep tEq rootSCon srcSCon by (metis (lifting) copy_def)
      next
        case False
        then have j2:"\<not>TypedStoSubpref p l (STArray x t) \<and> \<not>TypedStoSubpref l p (STArray x t)"
          using CompStoType_imps_TypedStoSubpref NotRelatedPrnt_imps_notRelatedChild f2 j1 rel
          by (meson NotReachablePrnt_imps_notReachableChild)
        moreover have "\<forall>subL. TypedStoSubpref subL l (STArray x t) \<longrightarrow> \<not> TypedStoSubpref subL p (STArray x t)"
          using NotRelatedPrnt_imps_notRelatedChild[of p l "(STArray x t)" "(STArray x t)"] j2 by blast
        moreover have "\<forall>subL. TypedStoSubpref subL p (STArray x t) \<longrightarrow> \<not> TypedStoSubpref subL l (STArray x t)"
          using j2 NotRelatedPrnt_imps_notRelatedChild by blast
        ultimately show ?thesis
          using copy_notSub_SCon copyStep tEq rootSCon srcSCon by (metis (lifting) copy_def)
      qed
    qed
  qed
qed


subsection \<open>Memory selection\<close>

lemma originalMConStillMCon:
  assumes "MCon struct (Memory st) x3"
    and "(\<forall>tloc loc. Toploc (Memory st) \<le> tloc \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<longrightarrow> accessStore loc (Memory st) = None)"
    and "\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) \<longrightarrow> accessStore locs (Memory st) = accessStore locs (Memory st')"
    and "\<forall>locs. \<not> TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) t' \<longrightarrow> accessStore
        locs (snd (allocate (Memory st))) = accessStore locs (Memory st')"
  shows " MCon struct (Memory st') x3" using assms(1)
proof(induction struct arbitrary: x3)
  case (MTArray x1 struct)
  have mcexp:"\<forall>i<x1.
(case accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) of None \<Rightarrow> False
| Some (MValue val) \<Rightarrow> (case struct of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon struct (Memory st) (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
| Some (MPointer loc2) \<Rightarrow> (case struct of MTArray len' arr' \<Rightarrow> MCon struct (Memory st) loc2 | MTValue Types \<Rightarrow> False))"
    using MTArray(2) unfolding MCon.simps by simp

  have "\<forall>i<x1.
(case accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') of None \<Rightarrow> False
| Some (MValue val) \<Rightarrow> (case struct of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon struct (Memory st') (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
| Some (MPointer loc2) \<Rightarrow> (case struct of MTArray len' arr' \<Rightarrow> MCon struct (Memory st') loc2 | MTValue Types \<Rightarrow> False))"
  proof(intros)
    fix i assume h1:"i<x1"
    show "case accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') of None \<Rightarrow> False
| Some (MValue val) \<Rightarrow> (case struct of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon struct (Memory st') (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
| Some (MPointer loc2) \<Rightarrow> (case struct of MTArray len' arr' \<Rightarrow> MCon struct (Memory st') loc2 | MTValue Types \<Rightarrow> False)"
    proof(cases "struct")
      case mta1:(MTArray x11 x12)
      then obtain v where vdef: "accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some (MPointer v)" using h1 mcexp
        using MTArray.prems(1) MConArrayPointers by blast
      then have vdef2:"accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some (MPointer v)" using assms(2) assms(3,4)
        by (metis nat_le_linear option.distinct(1))
      have "MCon struct (Memory st) v" using vdef mcexp h1 mta1 by fastforce
      then have "MCon struct (Memory st') v" using MTArray.IH[of v]
        by simp
      then show ?thesis using mta1 h1 vdef vdef2 by simp
    next
      case (MTValue x2)
      then obtain v where vdef: "accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some (MValue v)" using h1 mcexp
        using MCon_sub_MTVal_imps_val MTArray.prems(1) by presburger
      then have vdef2:"accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some (MValue v)" using assms
        by (metis nat_le_linear option.distinct(1))
      have "MCon struct (Memory st) (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using vdef mcexp h1 MTValue by auto
      then show ?thesis using MTValue vdef vdef2 h1 by auto
    qed
  qed

  moreover have "x3 \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st)))"
    using MCon_imps_Some MTArray.prems LSubPrefL2_def assms(2) not_None_eq by blast
  moreover have " \<not> TypedMemSubPref x3 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Memory st))) t'" using assms
    by (metis (no_types, opaque_lifting) MCon_imps_Some MTArray.prems LSubPrefL2_def Not_Sub_More_Specific le_refl neg_MemLSubPrefL2_imps_TypedMemSubPref not_Some_eq)
  moreover have "((\<exists>p. accessStore x3 (Memory st') = Some (MPointer p)) \<or> accessStore x3 (Memory st') = None)"
    using allocateSameAccess MTArray.prems calculation assms
    by (metis MCon.simps(2))

  ultimately show ?case unfolding MCon.simps
    by (metis MTArray.prems(1) MCon.simps(2))
next
  case (MTValue x')
  then show ?case using assms
    by (metis Option.option.simps(4) le_eq_less_or_eq MCon.simps(1))
qed


lemma mselReturnAlwaysHash:
  assumes"msel True t l'' x22 env cd st g = Normal ((l, t'), g')"
    and "TypeSafe env (Accounts st) (Stack st) (Memory st) (Storage st) cd"
    and "MCon t (Memory st) l''"
    and "fullyInitialised env (Accounts st) (Stack st)"
  shows "\<exists>prnt i len arr len' arr'. t= MTArray len arr \<and> l = hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<and> arr' = t'
      \<and> i < len' \<and> MCon (MTArray len' arr') (Memory st) prnt
                        \<and> (prnt = l'' \<and> len = len' \<and> arr' = arr \<or> CompMemType (Memory st) len arr (MTArray len' arr') l'' prnt) " using assms(1,3)
proof(induction "x22" arbitrary: t l'' g)
  case Nil
  then show ?case using msel.simps by simp
next
  case (Cons a x22)
  show ?case using Cons(2)
  proof(cases rule: msel.elims )
    case (1 _ _ _ _ _ g)
    then show ?thesis by blast
  next
    case (2 _ _ _ _ _ _ g)
    then show ?thesis by auto
  next
    case (3 al t loc x env cd st g)
    then obtain kv b g4' where a20: "local.expr x env cd st g = Normal ((KValue kv, Value (TUInt b)), g4')"
      and a30: "less (TUInt b) (TUInt b256) kv (ShowL\<^sub>i\<^sub>n\<^sub>t (int al)) = Some ((ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True), TBool)"
      using msel.simps(3) by (simp split: result.split_asm prod.split_asm types.split_asm type.split_asm if_split_asm stackvalue.split_asm option.split_asm memoryvalue.split_asm)
    then have b2:"(hash loc kv, t) = (l, t')" using 3 by simp
    have a50: "checkUInt b kv" using exprTypeconInduct(3) 3(1) assms(2) a20 typeCon.simps(2)[of b "extractValueType (KValue kv)"] extractValueType.simps(1)[of kv]
      using "3"(4,5,6) using assms(4) by force
    then have a60:"ReadL\<^sub>i\<^sub>n\<^sub>t(kv) < int al " using a20 a30 less_def plift.simps(2)[of "(<)" b b256 kv
        "(ShowL\<^sub>i\<^sub>n\<^sub>t (int al))"] Read_ShowL_id[of "(int al)"] unfolding createBool_def
        ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l_def by (simp split:if_split_asm)
    then have a62:"0\<le>ReadL\<^sub>i\<^sub>n\<^sub>t(kv)" and a65:"(ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t kv)) = kv" using a50 checkUInt_def[of b kv] by simp+
    have a64:"(ShowL\<^sub>n\<^sub>a\<^sub>t (nat (ReadL\<^sub>i\<^sub>n\<^sub>t kv))) = kv" using ShowLnat_ReadLint_inverse a62 a50 unfolding checkUInt_def by simp
    then have a70:"(nat (ReadL\<^sub>i\<^sub>n\<^sub>t kv)) \<in> {0..al-1}" using a60 a62 by simp
    have "loc = l''" using 3 by simp
    moreover have "(nat (ReadL\<^sub>i\<^sub>n\<^sub>t kv)) < al" using a70
      by (simp add: a60 a62 nat_less_iff)
    ultimately show ?thesis using b2 a64 a70 "3"(1) prod.inject
      by (metis Cons.prems(2))

  next
    case (4 al t'' loc x y ys env cd st g'')
    then obtain kv b g4' ptr where a20: "local.expr x env cd st g'' = Normal ((KValue kv, Value (TUInt b)), g4')"
      and a30: "less (TUInt b) (TUInt b256) kv (ShowL\<^sub>i\<^sub>n\<^sub>t (int al)) = Some ((ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True), TBool)"
      and a40:"accessStore (hash loc kv) (if True then Memory st else cd) = Some (MPointer ptr)"
      using msel.simps(3) by (simp split: result.split_asm prod.split_asm types.split_asm type.split_asm if_split_asm stackvalue.split_asm option.split_asm memoryvalue.split_asm)
    have a50: "checkUInt b kv" using exprTypeconInduct(3) 4(1) assms(2) a20 typeCon.simps(2)[of b "extractValueType (KValue kv)"] extractValueType.simps(1)[of kv]
      using "4"(4,5,6) using assms(4) by force
    then have a60:"ReadL\<^sub>i\<^sub>n\<^sub>t(kv) < int al " using a20 a30 less_def plift.simps(2)[of "(<)" b b256 kv
        "(ShowL\<^sub>i\<^sub>n\<^sub>t (int al))"] Read_ShowL_id[of "(int al)"] unfolding createBool_def
        ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l_def by (simp split:if_split_asm)
    then have a62:"0\<le>ReadL\<^sub>i\<^sub>n\<^sub>t(kv)" and a65:"(ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t kv)) = kv" using a50 checkUInt_def[of b kv] by simp+
    have a64:"(ShowL\<^sub>n\<^sub>a\<^sub>t (nat (ReadL\<^sub>i\<^sub>n\<^sub>t kv))) = kv" using ShowLnat_ReadLint_inverse a62 a50 unfolding checkUInt_def by simp
    then have a70:"(nat (ReadL\<^sub>i\<^sub>n\<^sub>t kv)) \<in> {0..al-1}" using a60 a62 by simp
    have tdef:"t = MTArray al t''" using 4 by simp
    then have mc:" MCon t'' (Memory st) ptr" using Cons.prems a40
      by (metis "4"(2,6) MCon_imps_sub_Mcon a60 a62 a64 nat_less_iff)

    then have mse:"msel True t'' ptr (y # ys) env cd st g4' = Normal ((l, t'), g')" using 4 a20 a30 a40 by simp
    then have "\<exists>prnt i len arr len' arr'.
       t'' = MTArray len arr \<and>
       l = hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<and> i < len' \<and> arr' = t' \<and> MCon (MTArray len' arr') (Memory st) prnt
           \<and> (prnt = ptr \<and> len = len' \<and> arr' = arr \<or> CompMemType (Memory st) len arr (MTArray len' arr') ptr prnt )"
      using Cons.IH[of t'' ptr g4'] 4(4,5,6,7,3) a64 mc by blast
    then obtain prnt i len arr len' arr' where defs:"t'' = MTArray len arr \<and>
       l = hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<and> i < len' \<and> arr' = t' \<and> MCon (MTArray len' arr') (Memory st) prnt
           \<and> (prnt = ptr \<and> len = len' \<and> arr' = arr \<or> CompMemType (Memory st) len arr (MTArray len' arr') ptr prnt )" by
           blast

    have a6:"(case t' of MTArray l' ar' \<Rightarrow> \<exists>p. accessStore l (if True then Memory st else cd) = Some (MPointer p)
                            \<and> CompMemType (if True then Memory st else cd) len arr t' ptr p
          | MTValue val \<Rightarrow> CompMemType (if True then Memory st else cd) len arr t' ptr l )"
      using exprTypeconInduct(1)[of True t'' ptr "(y # ys)" env cd st g4' l t' g'] mse mc assms(2) 4 defs
      using assms(4) unfolding fullyInitialised_def by simp

    then show ?thesis
    proof(cases "prnt = ptr")
      case True
      have notComp:"\<not>CompMemType (Memory st) len arr (MTArray len' arr') ptr prnt"
      proof
        assume in1:"CompMemType (Memory st) len arr (MTArray len' arr') ptr prnt"
        show False
        proof(cases "arr")
          case (MTArray x11 x12)
          then have "(\<exists>i<len. \<exists>l. accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some (MPointer l) \<and>
                    (l = prnt \<and> MTArray x11 x12 = MTArray len' arr' \<or> CompMemType (Memory st) x11 x12 (MTArray len' arr') l prnt))"
            using in1 CompMemType.simps(2)[of "Memory st" len x11 x12 "(MTArray len' arr')" ptr prnt] by auto
          moreover have " MCon (MTArray len (MTArray x11 x12)) (Memory st) ptr" using mc defs MTArray by simp
          ultimately show ?thesis using True in1 mc defs
            by (metis BothMConImpsNotCompMemType)
        next
          case (MTValue x2)
          then show ?thesis using in1 True by simp
        qed
      qed

      then have lenIslen':"len = len'" using defs mc a6 notComp by simp
      then have arrIsarr':"arr' = arr" using defs mc a6 notComp by blast

      then have notSame:"ptr \<noteq> l''" using defs mc 4
        using Cons.prems(2) MConSubTypes CompMemJustType.simps(2) by blast
      have "CompMemType (Memory st) al (MTArray len arr) (MTArray len' arr') loc prnt "
        using CompMemType.simps(2)[of "Memory st" al len arr "(MTArray len' arr')" loc prnt] a40 True defs lenIslen' arrIsarr'
        by (metis a60 a62 a64 nat_less_iff)
      moreover have "arr' = t'" using defs by simp
      ultimately show ?thesis using tdef True defs notSame
        using "4"(6,2) by blast
    next
      case False
      then have "CompMemType (Memory st) len arr (MTArray len' arr') ptr prnt" using defs by auto
      then have "CompMemType (Memory st) al (MTArray len arr) (MTArray len' arr') loc prnt"
        using CompMemType.simps(2)[of "Memory st" al len arr "(MTArray len' arr')" loc prnt] a40
        by (metis a60 a62 a64 nat_less_iff)
      then show ?thesis using tdef defs "4"(2,6) by blast
    qed
  qed
qed

lemma lexpIndexMem:
  assumes "lexp lv env cd st g = Normal ((LMemloc l, type.Memory t'), g')"
    and "TypeSafe env (Accounts st) (Stack st) (Memory st) (Storage st) cd"
    and "fullyInitialised env (Accounts st) (Stack st)"

obtains (1) x21 x22 tp tParent l' l'' prnt len' arr' i
where "lv = Ref x21 x22"
  and "(tp, Stackloc l') |\<in>| fmran (Denvalue env)"
  and "accessStore l' (Stack st) = Some (KMemptr l'')"
  and "tp = type.Memory tParent"
  and "MCon tParent (Memory st) l''"
  and "accessTypeStore l (Memory st) = Some (t')"
  and "(\<exists>len arr. tParent = MTArray len arr \<and>
      (case t' of MTArray l' ar' \<Rightarrow>
          \<exists>p. accessStore l (Memory st) = Some (MPointer p) \<and> CompMemType (Memory st) len arr t' l'' p
      | MTValue val \<Rightarrow> CompMemType (Memory st) len arr t' l'' l )
\<and> l = hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<and> i < len' \<and> arr' = t' \<and> MCon (MTArray len' arr') (Memory st) prnt
    \<and> (prnt = l'' \<and> len = len' \<and> arr' = arr \<or> CompMemType (Memory st) len arr (MTArray len' arr') l'' prnt))"
proof(cases lv)
  case (Id x1)
  then show ?thesis using assms(1) lexp.simps(1)[of x1] by (auto split:option.splits denvalue.splits)
next
  case (Ref x21 x22)
  then obtain tp l' where tpdef:"Denvalue env $$ x21 = Some (tp, Stackloc l')"
    using assms(1) lexp.simps(2)[of x21 x22 env cd "st"]
    by (auto split:option.splits denvalue.splits type.splits result.splits)
  then have parentIn:"( tp, Stackloc l') |\<in>| fmran (Denvalue env)" using fmranI by metis
  then obtain l'' where access:"accessStore l' (Stack st) = Some (KMemptr l'')"
    using Ref assms(1) lexp.simps(2)[of x21 x22 env cd "st"] tpdef
    by (auto split:option.splits denvalue.splits type.splits result.splits stackvalue.splits)
  then obtain t where tdef:"tp = type.Memory t" using access tpdef Ref assms(1) lexp.simps(2)[of x21 x22 env cd "st"]
    by (auto split:option.splits denvalue.splits type.splits result.splits stackvalue.splits)
  then have msel12:"msel True t l'' x22 env cd st g = Normal ((l, t'), g')" using access tpdef Ref assms(1) lexp.simps(2)[of x21 x22 env cd "st"]
    by (auto split:option.splits denvalue.splits type.splits result.splits stackvalue.splits prod.splits)
  have " MCon t (Memory st) l''"
    using access assms(2) parentIn sameMemTSafe tdef by blast
  then obtain prnt i len arr len' arr' where a1:"
     t = MTArray len arr \<and> l = hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<and> arr' = t' \<and> i < len' \<and> MCon (MTArray len' arr') (Memory st) prnt
    \<and> (prnt = l'' \<and> len = len' \<and> arr' = arr \<or> CompMemType (Memory st) len arr (MTArray len' arr') l'' prnt)"
    using mselReturnAlwaysHash[OF msel12 assms(2)] assms(3) unfolding fullyInitialised_def by blast

  have mconP:"MCon t (Memory st) l''" using tpdef access tdef assms(2)
    by (meson assms(2) fmranI sameMemTSafe)
  have "x22 \<noteq> []" using msel12 msel.simps by auto
  then have a6:"(\<exists>len arr.
       t = MTArray len arr \<and>
       (case t' of
        MTArray l' ar' \<Rightarrow>
          \<exists>p. accessStore l (Memory st) = Some (MPointer p) \<and>
              CompMemType (Memory st) len arr t' l'' p
        | MTValue val \<Rightarrow> CompMemType (Memory st) len arr t' l'' l ))"
    using exprTypeconInduct(1)[of True t l'' x22 env cd "st" g l t' g'] assms(2) mconP msel12 assms(3) unfolding fullyInitialised_def
    by presburger

  have "((case t of MTArray len arr \<Rightarrow> \<forall>i<len. accessTypeStore (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr
       | MTValue val \<Rightarrow> accessTypeStore l'' (Memory st) = Some (MTValue val)))"
    using assms(2) unfolding TypeSafe_def denvalueTypeCorrectness_def
    using parentIn tdef access
    using a6 by fastforce
  then have a10:"(\<forall>i<len. accessTypeStore (hash l'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr)" using a1 by simp

  have co:" (\<forall>locs tp.
      accessTypeStore locs (Memory st) = Some tp \<longrightarrow>
      (case accessStore locs (Memory st) of None \<Rightarrow> False
       | Some (MValue v) \<Rightarrow> \<exists>val. MCon tp (Memory st) locs \<and> tp = MTValue val \<and> accessTypeStore locs (Memory st) = Some tp
       | Some (MPointer p) \<Rightarrow> \<exists>len arr. MCon tp (Memory st) p \<and> tp = MTArray len arr
                            \<and> (\<forall>i<len. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr)
                           ))"
    using assms(2) unfolding TypeSafe_def subPrefixStructuralConsistency_def by blast

  have "accessTypeStore l (Memory st) = Some t'"
  proof(cases "prnt = l'' \<and> len = len' \<and> arr' = arr ")
    case True
    then show ?thesis using a1 a10 by blast
  next
    case False
    then have cmp:"CompMemType (Memory st) len arr (MTArray len' arr') l'' prnt" using a1 by blast
    have accTT:"\<forall>i<len'. accessTypeStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr'"
      using CompMemTypeSubIndexes[OF cmp ] a1 assms(2) unfolding TypeSafe_def
      using a10 mconP by argo
    then show ?thesis using a1 by simp
  qed

  then show ?thesis using msel12 1[OF Ref parentIn access tdef mconP, of prnt i len' arr' ] a1 a6 by blast
qed

lemma lexpStorageG:
  assumes "TypeSafe env (Accounts st) (Stack st) (Memory st) (Storage st) cd"

and "lexp lv env cd (st\<lparr>Gas := g\<rparr>) g = Normal ((LStoreloc locChanged, type.Storage t'),g')"
and "fullyInitialised env (Accounts st) (Stack st)"

obtains (1)
  "((type.Storage t', Storeloc locChanged) |\<in>| fmran (Denvalue env))"
| (2) l t
where "((type.Storage t, Storeloc l) |\<in>| fmran (Denvalue env))"
  and "(TypedStoSubpref locChanged l t \<and> CompStoType t t' l locChanged)"

| (3) l' t l
where "((type.Storage t, Stackloc l) |\<in>| fmran (Denvalue env))"
  and "accessStore l (Stack st) = Some (KStoptr l')"
  and "(TypedStoSubpref locChanged l' t \<and> CompStoType t t' l' locChanged)"
proof (cases lv)
  case (Id x1)
  then have "lexp (Id x1) env cd (st\<lparr>Gas := g\<rparr>) g = Normal ((LStoreloc locChanged, type.Storage ( t')), g')" using assms(2) by simp
  then have "Denvalue env $$ x1 = Some (type.Storage ( t'), Storeloc locChanged) "
    using Id lexp.simps(1)[of x1 env cd "(st\<lparr>Gas := g\<rparr>)" g] by (auto split:option.splits denvalue.splits)
  then show ?thesis by (simp add: "1" fmranI)
next
  case (Ref x21 x22)
  then have *: "lexp (Ref x21 x22) env cd (st\<lparr>Gas := g\<rparr>) g = Normal ((LStoreloc locChanged, type.Storage ( t')), g')" using assms(2) by simp
  then show ?thesis
  proof(cases "Denvalue env $$ x21")
    case None
    then show ?thesis using * lexp.simps(2) Ref by simp
  next
    case (Some a)
    then obtain tp loc where adef:"a = (type.Storage tp, loc)" using * lexp.simps(2) Ref by (cases a; (auto split: result.splits type.splits denvalue.splits option.splits stackvalue.splits))
    then have b6:"(type.Storage tp, loc) |\<in>| fmran (Denvalue env)" using Some by (simp add: fmranI)

    then show ?thesis
    proof(cases loc)
      case (Stackloc x1)
      then show ?thesis
      proof(cases "accessStore x1 (Stack st)")
        case None
        then show ?thesis using * Ref Stackloc lexp.simps(2)[of x21 x22 env cd "(st\<lparr>Gas := g\<rparr>)" g] Some adef by simp
      next
        case some2:(Some a)
        then obtain x4 where x4def:"a = KStoptr x4" using * Ref Stackloc lexp.simps(2)[of x21 x22 env cd "(st\<lparr>Gas := g\<rparr>)" g] Some adef some2 by (cases a; auto)
        then obtain l'' t'' where b20:"ssel tp x4 x22 env cd (st\<lparr>Gas := g\<rparr>) g = Normal ((l'', t''), g')"
          using Stackloc Some Ref * lexp.simps(2) adef some2 by (auto split: result.splits type.splits)
        have b10:"SCon tp x4 (Storage st (Address env))" using assms b6 some2 Stackloc x4def unfolding TypeSafe_def typeCompat_def by fastforce
        then have b30:"locChanged = l'' \<and> ( t') = t''" using * lexp.simps(2) Ref adef Stackloc b20 some2 x4def Some Ref b6 by simp

        then show ?thesis
        proof(cases x22)
          case Nil
          then have b25:"tp = t'' \<and> x4 = l''" using b20 ssel.simps(1) by simp
          then have b30:"locChanged = l'' \<and> ( t') = t''" using * lexp.simps(2) Ref adef Stackloc some2 x4def b20 Some Ref b6 by simp
          then show ?thesis using b6 3 b25 Stackloc some2 x4def
            using CompStoType_sameLocNdTyp TypedStoSubpref_sameLoc by auto
        next
          case (Cons a list)
          then have b10:"CompStoType tp t'' x4 l''"
            using exprTypeconInduct(2)[of tp x4 x22 env cd "(st\<lparr>Gas := g\<rparr>)" g l'' t'' g'] assms
            unfolding fullyInitialised_def using b10 b20 some2 x4def by simp
          have b30:"l'' = locChanged \<and> (t') = t''" using * lexp.simps(2) Ref adef Stackloc some2 x4def b20 Some Ref b6 by simp
          then have "CompStoType tp (t') x4 l''" using b10 by simp
          then show ?thesis using * lexp.simps(2) Ref adef Stackloc some2 x4def b20 Some Ref b6 b10 b30 3
            using CompStoType_imps_TypedStoSubpref by blast
        qed
      qed
    next
      case (Storeloc x2)
      then have b10:"SCon tp x2 (Storage st (Address env))" using assms b6 unfolding TypeSafe_def typeCompat_def by force
      then obtain l'' t'' where b20:"ssel tp x2 x22 env cd (st\<lparr>Gas := g\<rparr>) g = Normal ((l'', t''), g')"
        using Storeloc Some Ref * lexp.simps(2) adef by (auto split: result.splits type.splits)
      then show ?thesis
      proof(cases x22)
        case Nil
        then have b25:"tp = t'' \<and> x2 = l''" using b20 ssel.simps(1) by simp
        then have b30:"locChanged = l'' \<and> (t') = t''" using * lexp.simps(2) Ref adef Storeloc b20 Some Ref b6 by simp
        then show ?thesis using b6 1 adef Some Ref * b25 b20 by (simp add: Storeloc)
      next
        case (Cons a list)
        then have b10:"CompStoType tp t'' x2 l''"
          using exprTypeconInduct(2)[of tp x2 x22 env cd "(st\<lparr>Gas := g\<rparr>)" g l'' t'' g'] b20 assms
          unfolding fullyInitialised_def using b10 b20 Storeloc by simp
        have b30:"l'' = locChanged \<and> (t') = t''" using * lexp.simps(2) Ref adef Storeloc b20 Some Ref b6 by simp
        then have "CompStoType tp (t') x2 l''" using b10 by simp
        then show ?thesis using b30 b6 2 adef Some Ref * b10 b20 Storeloc
          using CompStoType_imps_TypedStoSubpref by blast
      qed
    qed
  qed
qed


subsection \<open>The state invariant\<close>

text \<open>@{text StateInvariant} is the conclusion of the main theorem. The resulting state is
  type-safe and fully initialised, and memory only grows: existing types, pointers and values
  are kept, unallocated locations below the old top stay unallocated, and the top location
  does not decrease.\<close>

definition allStoresSCon::"(address \<Rightarrow> storageT) \<Rightarrow> bool"
  where "allStoresSCon stoN = (\<forall>e ct t' l'. ep $$ Contract e = Some ct
\<and> (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue (e::environment)) \<longrightarrow> (SCon t' l' (stoN (Address (e::environment)))))"


definition StateInvariant :: "environment \<Rightarrow> state \<Rightarrow> state \<Rightarrow> calldataT \<Rightarrow> bool" where
  "StateInvariant ev st_orig st_curr cd \<equiv>
     TypeSafe ev (Accounts st_curr) (Stack st_curr) (Memory st_curr) (Storage st_curr) cd \<and>
     fullyInitialised ev (Accounts st_curr) (Stack st_curr) \<and>
     (\<forall>locs t. accessTypeStore locs (Memory st_orig) = Some t \<longrightarrow> accessTypeStore locs (Memory st_curr) = Some t) \<and>
(\<forall>locs v. accessStore locs (Memory st_orig) = Some (MPointer v) \<longrightarrow> (\<exists>v'. accessStore locs (Memory st_curr) = Some (MPointer v'))) \<and>
(\<forall>locs v. accessStore locs (Memory st_orig) = Some (MValue v) \<longrightarrow> (\<exists>v'. accessStore locs (Memory st_curr) = Some (MValue v'))) \<and>
(\<forall>i loc. i < Toploc (Memory st_orig) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<longrightarrow>
                      accessStore loc (Memory st_orig) = None \<longrightarrow> accessStore loc (Memory st_curr) = None) \<and>
  Toploc (Memory st_orig) \<le> Toploc (Memory st_curr)
    "


subsection \<open>Memory-to-memory copies\<close>

lemma cpm2m_subPrefixPersist:
  assumes "subPrefixStructuralConsistency mo"
    and "accessStore (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo)) mo = None"
    and "SomeValSomeTyp mo"
    and sameTypeAccess:"\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo)) \<or> locs = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo)) \<longrightarrow>
                         accessTypeStore locs (mo) = accessTypeStore locs m"
    and lessThan:"lessThanTopLocs mo"
    and sameTypeAccess2:" \<forall>locs. \<not> TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo)) (MTArray x t) \<or> locs =
        (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo)) \<longrightarrow>
       accessTypeStore locs (mo) = accessTypeStore locs m"
    and tps:"\<forall>destl'.
     TypedMemSubPref destl' (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo)) (MTArray x t) \<longrightarrow>
     (\<exists>stt. CompMemType m x t stt (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo)) destl' \<and>
           (case stt of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some parent_arr
            | MTValue pval \<Rightarrow> accessTypeStore destl' m = Some (MTValue pval)))"
    and MCondest:" MCon (MTArray x t) m (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (mo)))"
    and selfPoint:"\<forall>l l'. TypedMemSubPref l (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo)) (MTArray x t) \<and> accessStore l m = Some (MPointer l') \<longrightarrow> l' = l"
    and tps2:"\<forall>i<x. accessTypeStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some t"
    and nonLocChanged:"\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo)) \<or> locs = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo))
                  \<longrightarrow> accessStore locs (mo) = accessStore locs m"
    and a32:"\<forall>locs. \<not> TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo)) (MTArray x t) \<longrightarrow> accessStore locs mo = accessStore locs m"
  shows "subPrefixStructuralConsistency (m)" unfolding subPrefixStructuralConsistency_def
proof intros
  fix locs tp
  assume in1:"accessTypeStore locs m = Some tp"
  show "case accessStore locs m of None \<Rightarrow> False
 | Some (MValue v) \<Rightarrow> \<exists>val. MCon tp m locs \<and> tp = MTValue val \<and> accessTypeStore locs m = Some tp
 | Some (MPointer p) \<Rightarrow>
     \<exists>len arr.
        MCon tp m p \<and>
        tp = MTArray len arr \<and>
        (\<forall>i<len. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some arr) "
  proof(cases " locs = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo)) ")
    case True
    then have "accessStore locs mo = None"
      by (simp add: assms(2))
    then have "accessTypeStore locs mo = None"
      using assms(3) unfolding SomeValSomeTyp_def by force
    then have "accessTypeStore locs m = None" using sameTypeAccess True by simp
    then show ?thesis using in1 by simp
  next
    case notTop:False
    then show ?thesis
    proof(cases "LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo))")
      case True
      then have "accessStore locs mo = None "
        using lessThan unfolding lessThanTopLocs_def by blast
      then have "accessTypeStore locs mo = None"
        using assms(3) unfolding SomeValSomeTyp_def by force
      then have "TypedMemSubPref locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo)) (MTArray x t)"
        using sameTypeAccess2 in1 by auto
      then obtain stt where sttDef:"( CompMemType m x t stt (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo)) locs \<and>
        (case stt of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some parent_arr
         | MTValue pval \<Rightarrow> accessTypeStore locs m = Some (MTValue pval)))" using tps by blast
      then have mcLocs: "MCon stt m locs"
        using CompTypeRemainsMCon MCondest by blast
      then show ?thesis
      proof(cases stt)
        case (MTArray x11 x12)

        then have mi:"t = MTArray x11 x12 \<and> (\<exists>i<x. accessStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some (MPointer locs)) \<or>
                  (\<exists>midP subL subA i. CompMemType m x t (MTArray subL subA) (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo)) midP \<and>
                    accessStore (hash midP (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some (MPointer locs) \<and> i < subL \<and> subA = MTArray x11 x12)"
          using CompMemType_imps_Mid[of m x t x11 x12 "(ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo))" locs] sttDef by simp

        then show ?thesis
        proof(cases "t = MTArray x11 x12 \<and> (\<exists>i<x. accessStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some (MPointer locs))")
          case True
          then obtain i where idef:"i<x \<and> accessStore (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo)) (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some (MPointer locs)"
            by blast
          then have isTop:"locs = (hash (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo)) (ShowL\<^sub>n\<^sub>a\<^sub>t i))"
            using selfPoint by auto
          then have tpDef:"t = tp" using tps2 in1 idef by simp
          have "accessStore locs m = Some (MPointer locs)"
            using MCondest idef isTop by blast
          moreover have "\<exists>len arr.
                 MCon tp m locs \<and>
                 tp = MTArray len arr \<and>
                 (\<forall>i<len. accessTypeStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some arr) \<and>
                 (\<forall>v. accessStore locs m = Some (MPointer v) \<longrightarrow> accessTypeStore locs m = Some (MTArray len arr))"
            using tpDef mcLocs True MTArray
            using in1 sttDef by fastforce
          ultimately show ?thesis using in1 MTArray mcLocs tps2 by auto
        next
          case False
          then have prefPtrs_imps_Pref:"\<forall>l. TypedMemSubPrefPtrs m x t (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo)) l
                                    \<longrightarrow> TypedMemSubPref l (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo)) (MTArray x t)"
            using selfPoint_imps_TypedMemSubPref[of " (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo))" x t m ] selfPoint by blast

          then obtain midP subL subA i
            where mid: "(CompMemType m x t (MTArray subL subA) (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo)) midP \<and>
                    accessStore (hash midP (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some (MPointer locs) \<and> i < subL \<and> subA = MTArray x11 x12)"
            using mi False by auto
          then have locD:"locs = (hash midP (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using selfPoint
            using CompMemType_imps_in_GetAllMemoryLocations_ptr MCondest memSet_selfPoint by blast
          then obtain st2 where st2D:"(CompMemType m x t st2 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo)) midP \<and>
         (case st2 of MTArray parent_len parent_arr \<Rightarrow> \<forall>i<parent_len. accessTypeStore (hash midP (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some parent_arr
          | MTValue pval \<Rightarrow> accessTypeStore midP m = Some (MTValue pval)))" using mid tps
            using CompMemTypeSameLocsSameType CompMemType_imps_TypedMemSubPrefPtrs prefPtrs_imps_Pref by blast
          then have "st2 = (MTArray subL subA)" using mid CompMemTypeSameLocsSameType MCondest by blast
          then have " \<forall>i<subL. accessTypeStore (hash midP (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some subA" using st2D by simp
          then have tpDef:"MTArray x11 x12 = tp" using in1 locD mid by simp
          moreover have "\<exists>len arr.
                         MCon tp m locs \<and>
                         tp = MTArray len arr \<and>
                         (\<forall>i<len. accessTypeStore (hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some arr) "
            using tpDef mcLocs True MTArray in1 sttDef by auto
          ultimately show ?thesis using mid locD by simp
        qed
      next
        case (MTValue x2)
        then obtain v where isVal:"accessStore locs m = Some (MValue v)" using mcLocs
          using MConAccessSame.simps(1) SameMCon_imps_MConAccessSame by blast
        have "\<exists>val. MCon tp m locs \<and> tp = MTValue val \<and> accessTypeStore locs m = Some tp"
          using mcLocs in1 sttDef MTValue by simp
        then show ?thesis using isVal by simp
      qed
    next
      case False
      then have sameAccT:"accessTypeStore locs mo = accessTypeStore locs m"
        using sameTypeAccess by blast
      have sameAcc:"accessStore locs mo = accessStore locs m"
        using False nonLocChanged by metis
      obtain a where acc1:"accessStore locs mo = Some a"
        using assms(3) sameAccT unfolding TypeSafe_def SomeValSomeTyp_def using in1 by auto
      then have old:"(case accessStore locs mo of
      Some (MValue v) \<Rightarrow> \<exists>val. MCon tp mo locs \<and> tp = MTValue val \<and> accessTypeStore locs mo = Some tp
   | Some (MPointer p) \<Rightarrow>
       \<exists>len arr.
          MCon tp mo p \<and>
          tp = MTArray len arr \<and>
          (\<forall>i<len. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mo = Some arr))"
        using assms(1) in1 sameAccT unfolding subPrefixStructuralConsistency_def by fastforce
      then show ?thesis
      proof(cases a)
        case (MValue x1)

        then show ?thesis using sameAccT acc1 old MValue a32 in1 MCon.simps sameAcc
          by (auto split:option.splits memoryvalue.splits)
      next
        case (MPointer x2)

        then have oo:"\<exists>len arr.
          MCon tp mo x2 \<and>
          tp = MTArray len arr \<and>
          (\<forall>i<len. accessTypeStore (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mo = Some arr) "
          using old acc1 by simp
        then have subs:"\<not> LSubPrefL2 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo)) x2 \<and>\<not> LSubPrefL2 x2 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo)) "
          using assms unfolding TypeSafe_def
          by (meson AllPtrsNotTop_MCon TypeSafe_def le_refl)
        have "MCon tp mo x2" using oo by simp
        then have "MCon tp m x2"
          using lessThanTop_topChange_MCon subs nonLocChanged lessThan by simp

        then have "\<exists>len arr.
     MCon tp m x2 \<and>
     tp = MTArray len arr \<and>
     (\<forall>i<len. accessTypeStore (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some arr) "
          using oo subs nonLocChanged by (simp add: Mutual_NonSub_SpecificNonSub sameTypeAccess)
        moreover have "accessStore locs m = Some (MPointer x2)"
          using MPointer sameAcc acc1 by simp
        ultimately show ?thesis by simp
      qed
    qed
  qed
qed

lemma cpm2m_singleLChange:
  assumes "MCon struct m x3"
  assumes structss:"(case struct of
       MTArray len arr \<Rightarrow>
         (\<forall>i<len. accessTypeStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some arr)
       | MTValue val \<Rightarrow> accessTypeStore x3 m = Some (MTValue val))"
    and "updateStore l (MPointer tloc) m = m'"
    and lOld2:"\<exists>p. accessStore l m = Some (MPointer p)"
    and accl:"accessTypeStore l (m) = Some (MTArray x t)"
    and MCondest2:"MCon (MTArray x t) m' (tloc)"
    and subPrefM:"subPrefixStructuralConsistency (m)"
    and NonChangeM'm:"\<forall>locs. locs \<noteq> l \<longrightarrow> accessStore locs m = accessStore locs m'"
  shows "MCon struct m' x3"
  using assms(1,2)
proof(induction struct arbitrary:x3)
  case (MTArray x11 x12)
  have accessL:"accessStore l m' = Some (MPointer tloc)"
    using assms unfolding updateStore_def accessStore_def by auto
  have oldexp:"(\<forall>i<x11.
          case accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m of None \<Rightarrow> False
          | Some (MValue val) \<Rightarrow>
              (case x12 of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon x12 m (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
          | Some (MPointer loc2) \<Rightarrow>
              (case x12 of MTArray len' arr' \<Rightarrow> MCon x12 m loc2 | MTValue val \<Rightarrow> False)) \<and>
      (\<exists>p. accessStore x3 m = Some (MPointer p) \<or> accessStore x3 m = None)"
    using MTArray.prems(1) unfolding MCon.simps by simp

  then have subs:"(\<forall>i<x11. accessTypeStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some x12)"
    using structss MTArray by simp

  have "(\<forall>i<x11.
          case accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' of None \<Rightarrow> False
          | Some (MValue val) \<Rightarrow>
              (case x12 of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon x12 m' (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
          | Some (MPointer loc2) \<Rightarrow>
              (case x12 of MTArray len' arr' \<Rightarrow> MCon x12 m' loc2 | MTValue val \<Rightarrow> False))"
  proof(intros)
    fix i assume idef:"i<x11"
    then consider (val1) val typw where "accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some (MValue val)
                              \<and> x12 = MTValue typw
                              \<and> MCon x12 m (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i))"
      | (ptr1) ptr l1 a1 where "accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some (MPointer ptr)
                            \<and> x12 = MTArray l1 a1
                            \<and> MCon x12 m ptr"
      using oldexp
      by (metis MCon_imps_sub_Mcon MTArray.prems(1) mtypes.distinct(1) gr_implies_not0 mcon_accessStore nat_neq_iff)
    then show "case accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' of None \<Rightarrow> False
| Some (MValue val) \<Rightarrow> (case x12 of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon x12 m' (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
| Some (MPointer loc2) \<Rightarrow> (case x12 of MTArray len' arr' \<Rightarrow> MCon x12 m' loc2 | MTValue val \<Rightarrow> False)"
    proof(cases)
      case val1
      then show ?thesis
      proof(cases "(hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) = l")
        case True
        then show ?thesis using True lOld2 val1 by simp
      next
        case False
        then have sameACC:"accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m'"
          using assms unfolding updateStore_def accessStore_def by auto
        then have "MCon x12 m' (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i))"
          using val1 unfolding MCon.simps by auto
        then show ?thesis using val1 sameACC by simp
      qed
    next
      case ptr1
      then have "\<forall>i<x11. accessTypeStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some x12" using subs by simp

      then show ?thesis
      proof(cases "(hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) = l")
        case True
        then have "accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some (MPointer (tloc))"
          using assms unfolding updateStore_def accessStore_def by auto

        moreover have "x12 = MTArray x t" using subs True idef MTArray.prems calculation accl by auto
        moreover have "MCon x12 m' (tloc)" using calculation MCondest2 by blast
        ultimately show ?thesis
          by (simp add: ptr1)
      next
        case False
        then have "case x12 of MTArray len arr \<Rightarrow> (\<forall>i<len. accessTypeStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some arr)
                  | MTValue val \<Rightarrow> accessTypeStore ptr m = Some (MTValue val)"
          using subPrefM unfolding subPrefixStructuralConsistency_def using MTArray.prems
          using ptr1 idef by fastforce
        then have "MCon x12 m' ptr"
          using MTArray.IH[of ptr] ptr1 by blast
        then show ?thesis
          using False NonChangeM'm ptr1 by auto
      qed
    qed
  qed
  then show ?case using MTArray.prems(1) unfolding MCon.simps
    by (metis NonChangeM'm accessL)
next
  case (MTValue x2)
  then show ?case
  proof(cases "x3 = l")
    case True
    then show ?thesis using accl
      using MTValue.prems(2) by auto
  next
    case False
    then have "accessStore x3 m = accessStore x3 (m')"
      using assms unfolding updateStore_def accessStore_def by auto
    then show ?thesis using MTValue unfolding MCon.simps by simp
  qed
qed

end

end
