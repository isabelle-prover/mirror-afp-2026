section \<open>Statement preservation\<close>

theory TypeSafe
  imports TypeSafe_Assign
begin

context typesafe_base
begin

text \<open>
  Successful statement execution preserves the state invariant when the initial
  state is type-consistent and the environment is fully initialised. The
  assumptions of locale @{locale typesafe_base} remain explicit prerequisites.
\<close>

text \<open>The proof is by induction over the statement semantics @{const stmt}, with one case per
  statement form. Each case shows that the resulting state is again type-safe, that the
  environment stays fully initialised, and that memory only grows (see
  @{const StateInvariant}).
  \<^item> \<open>SKIP\<close> is immediate; \<open>COMP\<close>, \<open>ITE\<close> and \<open>WHILE\<close> follow from the induction hypotheses.
  \<^item> The sixteen forms of \<open>ASSIGN\<close> are proved separately in @{text TypeSafe_Assign}.
  \<^item> \<open>INVOKE\<close>, \<open>EXTERNAL\<close> and \<open>NEW\<close> run a body in a freshly initialised environment and use
    the initialisation results of @{text TypeSafe_Environment} with the induction hypothesis.
  \<^item> \<open>TRANSFER\<close> uses the balance lemmas of @{text TypeSafe_Base_Types}.
  \<^item> The two forms of \<open>BLOCK\<close> use the declaration results of @{text TypeSafe_Decl}.\<close>

theorem TypeSafe_Statements:
  assumes "TypeSafe ev (Accounts st) (Stack st) (Memory st) (Storage st) cd"
    and normal:"stmt smt ev cd st = Normal((),st')"
    and inits:"fullyInitialised ev (Accounts st) (Stack st)"
  shows "StateInvariant ev st st' cd"
  using assms(1,2,3)
proof (induction arbitrary: st' rule:stmt.induct)
  case (1 e cd st)
  have *:"st' = st\<lparr>Gas := (state.Gas st) - costs SKIP e cd st\<rparr>" using 1 skip by simp
  moreover have "Stack st = Stack st'" using * by simp
  moreover have memSame:"Memory st' = Memory st" using * by simp
  moreover have "Storage st' = Storage st" using * by simp
  moreover have "Accounts st' = Accounts st" using * by simp
  moreover have "WrittenMem_between (Memory st) (Memory st') = {}" using calculation unfolding WrittenMem_between_def by simp
  moreover have "ReachableMem e (Stack st') (Memory st') = ReachableMem e (Stack st) (Memory st)" unfolding ReachableMem.simps using calculation by metis

  ultimately show ?case using assms 1 * unfolding StateInvariant_def fullyInitialised_def by auto
next
  case (2 lv ex env cd st)
  then show ?case
  proof (cases rule:assign[OF 2(2)])
    case (1 v t2 g l2 t' g' v')
    from 2 1 show ?thesis by (rule TypeSafe_Assign_1)
  next
    case subcase2:(2 v t2 g locationChanged t' g' v')
    from 2 subcase2 show ?thesis by (rule TypeSafe_Assign_2)
  next
    case (3 v t g l t' g' v')
    from 2 3 show ?thesis by (rule TypeSafe_Assign_3)
  next
    case (4 p x t g l g' p' m t' st'')
    from 2 4 show ?thesis by (rule TypeSafe_Assign_4)
  next
    case (5 p x t g l t' g' p' s)
    from 2 5 show ?thesis by (rule TypeSafe_Assign_5)
  next
    case (6 p x t g l t' g' s)
    from 2 6 show ?thesis by (rule TypeSafe_Assign_6)
  next
    case (7 p x t g l t' g' m m')
    from 2 7 show ?thesis by (rule TypeSafe_Assign_7)
  next
    case (8 p x t g l t' g')
    from 2 8 show ?thesis by (rule TypeSafe_Assign_8)
  next
    case (9 p x t g l t' g' p' s)
    from 2 9 show ?thesis by (rule TypeSafe_Assign_9)
  next
    case (10 p x t g l t' g' s)
    from 2 10 show ?thesis by (rule TypeSafe_Assign_10)
  next
    case (11 p x t g l t' g')
    from 2 11 show ?thesis by (rule TypeSafe_Assign_11)
  next
    case (12 p x t g l t' g' p' m st'')
    from 2 12 show ?thesis by (rule TypeSafe_Assign_12)
  next
    case (13 p x t g l t' g')
    from 2 13 show ?thesis by (rule TypeSafe_Assign_13)
  next
    case (14 p x t g l t' g' s)
    from 2 14 show ?thesis by (rule TypeSafe_Assign_14)
  next
    case (15 p x t g l t' g' m m')
    from 2 15 show ?thesis by (rule TypeSafe_Assign_15)
  next
    case (16 p t g' g l t'' t')
    from 2 16 show ?thesis by (rule TypeSafe_Assign_16)
  qed
next
  case (3 s1 s2 e cd st)
  show ?case
  proof(cases "state.Gas st > costs (COMP s1 s2) e cd st")
    case True
    then have a5:"assert Gas (\<lambda>st. costs (COMP s1 s2) e cd st < state.Gas st) st = Normal ((), st)" by simp
    then obtain sgas where *:"sgas = st\<lparr>Gas := state.Gas st - costs (COMP s1 s2) e cd st\<rparr>" by simp
    then have a6:"modify (\<lambda>st. st\<lparr>Gas := state.Gas st - costs (COMP s1 s2) e cd st\<rparr>) st = Normal ((), sgas)" by simp
    moreover have sStackSame:"Stack st = Stack sgas" using * by simp
    moreover have sgasSame:"Memory st = Memory sgas" using * by simp
    moreover have "Storage st = Storage sgas" using * by simp
    moreover have "Accounts st = Accounts sgas" using * by simp
    ultimately have a10:"TypeSafe e (Accounts sgas) (Stack sgas) (Memory sgas) (Storage sgas) cd"
      using 3(3) TypeSafe_def True by simp
    then obtain sts1 where s1:"stmt s1 e cd sgas = Normal ((), sts1)" using 3 * stmt.simps(3) comp by meson
    have fi:"fullyInitialised e (Accounts sgas) (Stack sgas)" using 3(5) unfolding fullyInitialised_def using * by simp
    then have cc0:"StateInvariant e sgas sts1 cd" using 3(1)[OF a5 a6 a10 s1] by blast

    then have ts: "TypeSafe e (Accounts sts1) (Stack sts1) (Memory sts1) (Storage sts1) cd"
      using a10 3(1)[of "()" st "()" sgas sts1] a5 a6 * s1 unfolding StateInvariant_def by simp
    then have "stmt s2 e cd sts1 = Normal ((),st')" using 3(4) * s1 using comp by fastforce
    then have cc2:"StateInvariant e sts1 st' cd" using 3(2)[of "()" st "()" sgas "()" "sts1" st'] a5 a6 * s1 ts fi
      using atype_same by (metis cc0 StateInvariant_def)
    then have cc5:"TypeSafe e (Accounts st') (Stack st') (Memory st') (Storage st') cd\<and>
  (\<forall>locs t. accessTypeStore locs (Memory sts1) = Some t \<longrightarrow> accessTypeStore locs (Memory st') = Some t)
\<and>(\<forall>i loc. i < Toploc (Memory sts1) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<longrightarrow> accessStore loc
    (Memory sts1) = None \<longrightarrow> accessStore loc (Memory st') = None)"
      unfolding StateInvariant_def by blast
    have cc10:"fullyInitialised e (Accounts st') (Stack st')\<and>
  (\<forall>locs t. accessTypeStore locs (Memory sts1) = Some t \<longrightarrow> accessTypeStore locs (Memory st') = Some t)
\<and> (\<forall>i loc. i < Toploc (Memory sts1) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<longrightarrow> accessStore loc
    (Memory sts1) = None \<longrightarrow> accessStore loc (Memory st') = None)"
      using cc2 unfolding StateInvariant_def by blast
    then have cc12:"TypeSafe e (Accounts sts1) (Stack sts1) (Memory sts1) (Storage sts1) cd \<and>
    fullyInitialised e (Accounts sts1) (Stack sts1)\<and>
    (\<forall>locs t. accessTypeStore locs (Memory sgas) = Some t \<longrightarrow> accessTypeStore locs (Memory sts1) = Some t) \<and>
(\<forall>i loc. i < Toploc (Memory sgas) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<longrightarrow> accessStore loc (Memory
    sgas) = None \<longrightarrow> accessStore loc (Memory sts1) = None)"
      using cc0 unfolding StateInvariant_def by simp
    have cc15:"TypeSafe e (Accounts st') (Stack st') (Memory st') (Storage st') cd \<and>
  fullyInitialised e (Accounts st') (Stack st') \<and>
  (\<forall>locs t. accessTypeStore locs (Memory sts1) = Some t \<longrightarrow> accessTypeStore locs (Memory st') = Some t)
\<and> (\<forall>i loc. i < Toploc (Memory sts1) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<longrightarrow> accessStore loc
    (Memory sts1) = None \<longrightarrow> accessStore loc (Memory st') = None)"
      using cc2 unfolding StateInvariant_def by blast
    have tlocs:"Toploc (Memory st) \<le> Toploc (Memory sts1) \<and> Toploc (Memory sts1) \<le> Toploc (Memory st')"
      using cc0 cc2 unfolding StateInvariant_def using sgasSame by simp
    then have "(\<forall>i loc. i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)
                \<longrightarrow> accessStore loc (Memory st) = None \<longrightarrow> accessStore loc (Memory st') = None)"
      using sgasSame cc15 cc12
      by (metis (no_types, lifting) dual_order.strict_trans1)
    then show ?thesis using cc5 cc10 cc15 cc12 unfolding StateInvariant_def
      using sgasSame
      using StateInvariant_def cc0 cc2 tlocs by auto
  next
    case False
    then have "assert Gas (\<lambda>st. costs (COMP s1 s2) e cd st < state.Gas st) st = Exception Gas" by simp
    then show ?thesis using 3(4) stmt.simps(3) by simp
  qed
next
  case (4 ex s1 s2 e cd st)
  then show ?case
  proof(cases "state.Gas st> costs (ITE ex s1 s2) e cd st")
    case True
    then have a5:"assert Gas (\<lambda>st. costs (ITE ex s1 s2) e cd st < state.Gas st) st = Normal ((), st)" by simp
    then obtain sgas where *:"sgas = st\<lparr>Gas := state.Gas st - costs (ITE ex s1 s2) e cd st\<rparr>" by simp
    then have a6:"modify (\<lambda>st. st\<lparr>Gas := state.Gas st - costs (ITE ex s1 s2) e cd st\<rparr>) st = Normal ((), sgas)" by simp
    moreover have "Stack st = Stack sgas" using * by simp
    moreover have "Memory st = Memory sgas" using * by simp
    moreover have "Storage st = Storage sgas" using * by simp
    moreover have "Accounts st = Accounts sgas" using * by simp
    ultimately have a10:"TypeSafe e (Accounts sgas) (Stack sgas) (Memory sgas) (Storage sgas) cd" using 4(3) True by simp
    then consider (atrue) g where "expr ex e cd sgas (state.Gas sgas) = Normal ((KValue (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True), Value TBool),g)"
      |(afalse) g where "expr ex e cd sgas (state.Gas sgas) = Normal ((KValue (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False), Value TBool),g)" using * 4(4) stmt.simps(4)
      by (simp split:if_split_asm result.split_asm prod.split_asm stackvalue.split_asm type.split_asm types.split_asm)
    then show ?thesis
    proof (cases)
      case atrue
      then obtain g where a20:"expr ex e cd sgas (state.Gas sgas) = Normal ((KValue (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True), Value TBool), g)" by simp
      then obtain s'' where a25:"s'' = sgas\<lparr>Gas:= g\<rparr>" by simp
      moreover have "Stack s'' = Stack sgas" using a25 by simp
      moreover have "Memory s'' = Memory sgas" using a25 by simp
      moreover have "Storage s'' = Storage sgas" using a25 by simp
      moreover have "Accounts s'' = Accounts sgas" using a25 by simp
      ultimately have "TypeSafe e (Accounts s'') (Stack s'') (Memory s'') (Storage s'') cd" using assms 4 True atrue a10 a25 by metis
      moreover have "stmt s1 e cd s'' = Normal((),st')" using * a20 stmt.simps(4) 4(4) a25 by (simp split:if_split_asm result.split_asm prod.split_asm)
      moreover have "fullyInitialised e (Accounts s'') (Stack s'')" using 4(5)
        using \<open>Accounts s'' = Accounts sgas\<close> \<open>Accounts st = Accounts sgas\<close>
        by (simp add: \<open>Stack s'' = Stack sgas\<close> \<open>Stack st = Stack sgas\<close>)
      ultimately have "StateInvariant e s'' st' cd" using 4(1)[of "()" st "()" sgas "(KValue (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True),
          Value TBool)" s'' "(ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True)" s'' st'] a5 a6 a20 a25
        unfolding StateInvariant_def by simp
      then show ?thesis unfolding StateInvariant_def
        using \<open>Memory s'' = Memory sgas\<close> \<open>Memory st = Memory sgas\<close> by simp
    next
      case afalse
      then obtain g where a20:"expr ex e cd sgas (state.Gas sgas) = Normal ((KValue (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False), Value TBool), g)" and
        a21: "expr ex e cd sgas (state.Gas sgas) \<noteq> Normal ((KValue (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True), Value TBool), g)" by fastforce
      then obtain s'' where a25:"s'' = sgas\<lparr>Gas:= g\<rparr>" by simp
      moreover have "Stack s'' = Stack sgas" using a25 by simp
      moreover have "Memory s'' = Memory sgas" using a25 by simp
      moreover have "Storage s'' = Storage sgas" using a25 by simp
      moreover have "Accounts s'' = Accounts sgas" using a25 by simp
      ultimately have "TypeSafe e (Accounts s'') (Stack s'') (Memory s'') (Storage s'') cd" using assms 4 True afalse a10 a25 by metis
      moreover have "stmt s2 e cd s'' = Normal((),st')" using * a20 a21 stmt.simps(4)[of ex s1 s2 e cd st ] 4(4) a25 by (simp split:if_split_asm result.split_asm prod.split_asm)
      moreover have "fullyInitialised e (Accounts s'') (Stack s'')" using 4(5) unfolding fullyInitialised_def
        using \<open>Accounts s'' = Accounts sgas\<close> \<open>Accounts st = Accounts sgas\<close>
        by (simp add: \<open>Stack s'' = Stack sgas\<close> \<open>Stack st = Stack sgas\<close>)
      moreover have "StateInvariant e s'' st' cd" using 4(2)[of "()" st "()" sgas "(KValue (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False),
          Value TBool)" s'' "(ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False)" s'' st']
          a5 a6 a20 a21 a25 calculation by auto
      ultimately show ?thesis
        unfolding StateInvariant_def
        using \<open>Memory s'' = Memory sgas\<close> \<open>Memory st = Memory sgas\<close> by auto
    qed
  next
    case False
    then show ?thesis using 4(4) stmt.simps(4) by simp
  qed
next
  case (5 ex s0 e cd st)
  show ?case
  proof(cases rule:while[OF 5(4)])
    case (1 g st'')
    then have a5:"assert Gas (\<lambda>st. costs (WHILE ex s0) e cd st < state.Gas st) st = Normal ((), st)" by simp
    then obtain sgas where *:"sgas = st\<lparr>Gas := state.Gas st - costs (WHILE ex s0) e cd st\<rparr>" by simp
    then have a6:"modify (\<lambda>st. st\<lparr>Gas := state.Gas st - costs (WHILE ex s0) e cd st\<rparr>) st = Normal ((), sgas)" by simp

    then have a10:"toState (expr ex e cd) sgas
          = Normal ((KValue (ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l True), Value TBool), (st\<lparr>Gas := g\<rparr>))" using 1 * by auto


    have a20:"TypeSafe e (Accounts (st\<lparr>Gas := g\<rparr>)) (Stack (st\<lparr>Gas := g\<rparr>)) (Memory (st\<lparr>Gas := g\<rparr>)) (Storage (st\<lparr>Gas := g\<rparr>)) cd"
      using 5(3) by simp
    have a25:"fullyInitialised e (Accounts (st\<lparr>Gas := g\<rparr>)) (Stack (st\<lparr>Gas := g\<rparr>))" using 5(5) unfolding fullyInitialised_def by simp
    then have a30:"StateInvariant e (st\<lparr>Gas := g\<rparr>) st'' cd"
      using 5(1)[OF a5 a6 a10 _ _ a20 1(3) ] unfolding StateInvariant_def by simp
    have cc0:"StateInvariant e st'' st' cd"
      using 5(2)[OF a5 a6 a10 _ _ 1(3) _ 1(4)] a30 unfolding StateInvariant_def by simp

    then have ts:"TypeSafe e (Accounts st') (Stack st') (Memory st') (Storage st') cd \<and>
  fullyInitialised e (Accounts st') (Stack st')" using cc0 unfolding StateInvariant_def by blast
    have "Memory st = Memory (st\<lparr>Gas := g\<rparr>) \<and> Stack st = Stack (st\<lparr>Gas := g\<rparr>)" by simp
    then show ?thesis using ts a30 cc0 unfolding StateInvariant_def by fastforce
  next
    case (2 g)
    then have "TypeSafe e (Accounts st') (Stack st') (Memory st') (Storage st') cd "
      by (simp add: "5.prems"(1))
    moreover have "fullyInitialised e (Accounts st') (Stack st')" using 2
      using "5.prems"(2,3) atype_same fullyInitialised_def by simp
    moreover have "Memory st = Memory st' \<and> Stack st = Stack st'" using 2 by simp
    ultimately show ?thesis unfolding StateInvariant_def by simp
  qed
next
  case (6 i xe e cd st)
  show ?case
  proof(cases rule:invoke[OF 6(3)])
    case (1 ct fb fp f e\<^sub>l cd\<^sub>l k\<^sub>l m\<^sub>l g st'')
    then have a5:"assert Gas (\<lambda>st. costs (INVOKE i xe) e cd st < state.Gas st) st = Normal ((), st)" by simp
    then obtain sgas where *:"sgas = st\<lparr>Gas := state.Gas st - costs (INVOKE i xe) e cd st\<rparr>" by simp
    then have a6:"modify (\<lambda>st. st\<lparr>Gas := state.Gas st - costs (INVOKE i xe) e cd st\<rparr>) st = Normal ((), sgas)" by simp
    have a10:"option Err (\<lambda>_. ep $$ Contract e) sgas = Normal ((ct, fb), sgas)" using 1(2) by simp
    then have a20:"(case ct $$ i of None \<Rightarrow> throw Err | Some (Method (fp, True, f)) \<Rightarrow> throw Err
     | Some (Method (fp, False, f)) \<Rightarrow> return (fp, f) | Some _ \<Rightarrow> throw Err)
     sgas = Normal ((fp, f), sgas)" using 1 by auto


    have memSGas:"Memory sgas = Memory st" using * by auto
    have a25:"applyf Memory sgas = Normal ((Memory sgas), sgas)" by auto

    obtain x where xDef:"x = ffold_init ct (emptyEnv (Address e) (Contract e) (Sender e) (Svalue e)) (fmdom ct)" by simp

    have tsX:"TypeSafe x (Accounts sgas) emptyStore (Memory sgas) (Storage sgas) emptyTypedStore"
      using ffoldInitTypeSafe[of "(Accounts sgas)" "(Storage sgas)" "Svalue e" "(Memory sgas)" _ ct fb "Address e" _ _]
      using * 6(2) "6.prems"(3) unfolding TypeSafe_def fullyInitialised_def using 1(2) xDef ffold_init_def by auto
    have cx:"Contract x = Contract e" using xDef by simp
    then have a27:"load False fp xe x emptyTypedStore emptyStore (Memory sgas) e cd (sgas) (state.Gas st - costs (INVOKE i xe) e cd st) =
    Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), g)" using 1(4) * xDef unfolding ffold_init_def by simp
    then have a30:"toState (load False fp xe x emptyTypedStore emptyStore (Memory sgas) e cd) sgas =
  Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), sgas\<lparr>Gas := g\<rparr>) " using * 1(5) by auto
    have sameADD:"Address e = Address x"
      by (simp add: xDef)
    have link:"TypeSafe e\<^sub>l (Accounts sgas) k\<^sub>l m\<^sub>l (Storage sgas) cd\<^sub>l \<and>
    fullyInitialised e\<^sub>l (Accounts sgas) k\<^sub>l \<and>
    (\<not> False \<longrightarrow>
     (\<forall>locs tp. MCon tp (Memory sgas) locs \<longrightarrow> MCon tp m\<^sub>l locs) \<and>
     Toploc (Memory sgas) \<le> Toploc m\<^sub>l \<and>
     ncpDenvalueLimit e\<^sub>l e k\<^sub>l (Stack sgas) (Memory sgas) \<and>
     ncpOMemInDMem (Memory sgas) m\<^sub>l \<and> ncpElementsNoSubPref (Memory sgas) m\<^sub>l \<and> ncpNewSelfPoint (Memory sgas) m\<^sub>l)"
    proof -
      have "(\<forall>locs tp. MCon tp (Memory sgas) locs \<longrightarrow> MCon tp (Memory sgas) locs)" by blast
      moreover have "Toploc (Memory sgas) \<le> Toploc (Memory sgas)" by simp
      moreover have "ncpDenvalueLimit x e emptyStore (Stack sgas) (Memory sgas)" unfolding ncpDenvalueLimit_def accessStore_def emptyStore_def by simp
      moreover have "ncpOMemInDMem (Memory sgas) (Memory sgas)" unfolding ncpOMemInDMem_def by blast
      moreover have "ncpElementsNoSubPref (Memory sgas) (Memory sgas)" using ncpElementsNoSubPref_sameMem 6(2) * by auto
      moreover have "ncpNewSelfPoint (Memory sgas) (Memory sgas)" unfolding ncpNewSelfPoint_def by auto
      moreover have "TypeSafe x (Accounts sgas) emptyStore (Memory sgas) (Storage sgas) emptyTypedStore"
        using ffoldInitTypeSafe[of "(Accounts sgas)" "(Storage sgas)" "Svalue e" "(Memory sgas)" e ct fb "Address e" _ _]
        using * 6(2) "6.prems"(3) unfolding TypeSafe_def fullyInitialised_def using 1(2) xDef ffold_init_def by auto
      moreover have fiE:"fullyInitialised e (Accounts sgas) (Stack sgas)"
        by (simp add: "*" "6.prems"(3))
      moreover have "fullyInitialised x (Accounts sgas) emptyStore"
      proof -
        have addX:"Address x = Address e" by (simp add: xDef)
        have typeX:"Type (Accounts sgas (Address x)) = Some (atype.Contract (Contract x))"
          using fiE addX cx unfolding fullyInitialised_def by force
        have epX:"ep $$ Contract x = Some (ct, fb)" using "1"(2) cx by simp
        have mapX:"\<forall>id v. (ct $$ id = Some (Var v)) = (Denvalue x $$ id = Some (type.Storage v, Storeloc id))"
          using xDef unfolding ffold_init_def
          using ffoldInit_var_storage_mapping_eq[of ct "Address e" "Contract e" "Sender e" "Svalue e" x]
          by blast
        have locX:"\<forall>id v loc. Denvalue x $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc"
        proof (intro allI impI)
          fix id v loc
          assume hx:"Denvalue x $$ id = Some (type.Storage v, Storeloc loc)"
          have "(Denvalue x $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> snd (type.Storage v, Storeloc loc) = Storeloc id)"
            using xDef unfolding ffold_init_def
            using ffoldInitAllLocsStorage[
              of ct "e" "e" "e" "Svalue e" "fmdom ct"
            ] by simp
          then show "id = loc" using hx by simp
        qed
        have ptrX:"\<forall>t l p.
            (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue x) \<and> accessStore l emptyStore = Some (KStoptr p) \<longrightarrow>
            (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue x) \<and> CompStoType t' t l' p)"
          by (simp add: accessStore_def emptyStore_def)
        show ?thesis
          unfolding fullyInitialised_def using typeX epX mapX locX ptrX by blast
      qed
      ultimately show ?thesis using exprTypeconInduct(4)[of False fp xe x emptyTypedStore emptyStore "Memory sgas" e cd "sgas" "(state.Gas st - costs (INVOKE i xe) e cd st)"
            e\<^sub>l cd\<^sub>l k\<^sub>l m\<^sub>l g] a27 6(2) * sameADD by auto
    qed
    then have a40:" TypeSafe e\<^sub>l (Accounts (st\<lparr>Gas := g, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)) (Stack (st\<lparr>Gas := g, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>))
     (Memory (st\<lparr>Gas := g, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)) (Storage (st\<lparr>Gas := g, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)) cd\<^sub>l" using * by auto

    have typeMstML:"\<forall>locs t. accessTypeStore locs (Memory st) = Some t \<longrightarrow> accessTypeStore locs (m\<^sub>l) = Some t "
    proof intros
      fix locs t
      assume in1:"accessTypeStore locs (Memory st) = Some t"
      then have "\<exists>v. accessStore locs (Memory st) = Some v" using 6(2) unfolding TypeSafe_def SomeValSomeTyp_def by auto
      then have "\<exists>i. i < Toploc (Memory sgas) \<and> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t i)"
        using 6(2) unfolding TypeSafe_def lessThanTopLocs_def using memSGas by presburger
      then have "accessTypeStore locs (Memory sgas) = accessTypeStore locs m\<^sub>l"
        using link unfolding ncpOMemInDMem_def by blast
      then show "accessTypeStore locs m\<^sub>l = Some t" using in1 memSGas by auto
    qed


    have a44:"(Address e\<^sub>l) = (Address e)" using xDef a27
      using emptyEnv_address ffold_init_ad ffold_init_def msel_ssel_expr_load_rexp_gas(4) by presburger
    moreover have a45:"Contract e\<^sub>l = Contract e" using xDef a27
      using emptyEnv_members ffold_init_contract ffold_init_def msel_ssel_expr_load_rexp_gas(4) by presburger
    ultimately have cc1:"(\<exists>c. Type (Accounts (st\<lparr>Gas := g, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>) (Address
        e\<^sub>l)) = Some (atype.Contract c) \<and> Contract e\<^sub>l = c)"
      using 6(4) unfolding fullyInitialised_def by simp

    have a60:"\<forall>id x'. Denvalue x $$ id = Some x' \<longrightarrow> Denvalue e\<^sub>l $$ id = Some x'"
      using load_denval_existing_remain(4)[of False fp xe x emptyTypedStore emptyStore "(Memory sgas)" e cd sgas "(state.Gas st - costs
          (INVOKE i xe) e cd st)" e\<^sub>l cd\<^sub>l k\<^sub>l m\<^sub>l g] a27 by blast


    have cc3:"(\<forall>t l p.
        (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e\<^sub>l) \<longrightarrow>
        accessStore l (Stack (st\<lparr>Gas := g, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)) = Some (KStoptr p) \<longrightarrow>
        (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e\<^sub>l) \<and> CompStoType t' t l' p))"
      using fullyInitialised_def link by auto

    have a50:" fullyInitialised e\<^sub>l (Accounts (st\<lparr>Gas := g, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)) (Stack
        (st\<lparr>Gas := g, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>))" using 6(4)
        cc1 fullyInitialised_def link by auto
    have cc10:"applyf Stack (sgas\<lparr>Gas := g\<rparr>) = Normal ((Stack st), sgas\<lparr>Gas := g\<rparr>)" using * by simp
    have IH1:"TypeSafe e\<^sub>l (Accounts st'') (Stack st'') (Memory st'') (Storage st'') cd\<^sub>l \<and> fullyInitialised e\<^sub>l (Accounts st'') (Stack st'')
                \<and>
    (\<forall>locs t. accessTypeStore locs (Memory (st\<lparr>Gas := g, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)) = Some t \<longrightarrow> accessTypeStore locs (Memory st'') = Some t) \<and>
(\<forall>locs v. accessStore locs (Memory (st\<lparr>Gas := g, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)) = Some (MPointer v)
    \<longrightarrow> (\<exists>v'. accessStore locs (Memory st'') = Some (MPointer v'))) \<and>
    (\<forall>locs v. accessStore locs (Memory (st\<lparr>Gas := g, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)) = Some (MValue v)
        \<longrightarrow> (\<exists>v'. accessStore locs (Memory st'') = Some (MValue v'))) \<and>
(\<forall>i loc.
        i < Toploc (Memory (st\<lparr>Gas := g, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<longrightarrow>
        accessStore loc (Memory (st\<lparr>Gas := g, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)) = None \<longrightarrow> accessStore loc (Memory st'') = None) \<and>
Toploc (Memory (st\<lparr>Gas := g, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)) \<le> Toploc (Memory st'')"
      using 6(1)[OF a5 a6 a10 _ a20 _ xDef a25 a30 _ _ _ cc10 _ a40 1(5) a50] * unfolding StateInvariant_def by simp
    have cc20:"(Memory st') = (Memory st'') \<and> (Accounts st'') = (Accounts st') \<and> (Storage st'') = (Storage st')" using 1(6) by simp
    have stackOver:"(Stack st') = (Stack st)" using 1(6) by auto


    show ?thesis unfolding TypeSafe_def StateInvariant_def
    proof intros
      show " AddressTypes (Accounts st')" using IH1 cc20 unfolding TypeSafe_def by auto
    next
      show "safeContract (Accounts st') (Storage st')" using IH1 cc20 unfolding TypeSafe_def by auto
    next
      show "unique_locations (Denvalue e)" using 6(2) unfolding TypeSafe_def by blast
    next
      show "compPointers (Stack st') (Denvalue e)" using 6(2) unfolding TypeSafe_def using cc20
        using stackOver by argo
    next
      show "balanceTypes (Accounts st')" using IH1 cc20 unfolding TypeSafe_def by auto
    next
      have "envAddressesWellFormed e" using 6(2) unfolding TypeSafe_def by blast
      then show "addressFormat (Address e)" and "addressFormat (Sender e)" by simp+
    next
      show "svalueTypes (Svalue e)" using 6(2) unfolding TypeSafe_def by blast
    next
      show "lessThanTopLocs (Stack st')" using 6(2) 1(6) unfolding TypeSafe_def by simp
    next
      show "lessThanTopLocs cd" using 6(2) unfolding TypeSafe_def by blast
    next
      show "lessThanTopLocs (Memory st')" using IH1 cc20 unfolding TypeSafe_def by auto
    next
      show " typeCompat (Denvalue e) (Stack st') (Memory st') (Storage st' (Address e)) cd"
        unfolding typeCompat_def
      proof intros
        fix tIn lIn
        assume in1:"(tIn, lIn) |\<in>| fmran (Denvalue e)"
        show "denvalueCon (Stack st') (Memory st') (Storage st' (Address e)) cd tIn lIn"
        proof (split denvalue.split, intros)
          fix x1 assume stackLoc:"lIn = Stackloc x1"
          show "case accessStore x1 (Stack st') of None \<Rightarrow> False
              | Some (KValue val) \<Rightarrow> (case tIn of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
              | Some (KCDptr stloc) \<Rightarrow> (case tIn of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
              | Some (KMemptr stloc) \<Rightarrow> (case tIn of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
              | Some (KStoptr stloc) \<Rightarrow> (case tIn of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address e)) | _ \<Rightarrow> False)"
          proof (split option.split, intros)
            assume "accessStore x1 (Stack st') = None"
            then show False using 6(2) unfolding TypeSafe_def typeCompat_def using stackOver in1
              by (metis "6.prems"(1) option.discI stackLoc typeSafeAllStacklocsExist)
          next
            fix x2 assume Some:"accessStore x1 (Stack st') = Some x2"
            then have SomeOld:"accessStore x1 (Stack st) = Some x2" using stackOver by simp
            show "case x2 of KValue val \<Rightarrow> (case tIn of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
          | KCDptr stloc \<Rightarrow> (case tIn of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
          | KMemptr stloc \<Rightarrow> (case tIn of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
          | KStoptr stloc \<Rightarrow> (case tIn of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address e)) | _ \<Rightarrow> False)"
            proof(split stackvalue.split, intros)
              fix x1 assume KValue:"x2 = KValue x1"
              then show "case tIn of Value typ \<Rightarrow> typeCon typ x1 | _ \<Rightarrow> False"
                using 6(2) unfolding TypeSafe_def typeCompat_def using stackLoc stackOver in1 Some SomeOld by force
            next
              fix x2a assume KCDPtr:"x2 = KCDptr x2a"
              then show "case tIn of Calldata struct \<Rightarrow> MCon struct cd x2a | _ \<Rightarrow> False"
                using 6(2) unfolding TypeSafe_def typeCompat_def using stackLoc stackOver in1 Some SomeOld by force
            next
              fix x3 assume KMemPtr:"x2 = KMemptr x3"
              then obtain struct where structDef:"tIn = type.Memory struct" using 6(2) unfolding TypeSafe_def typeCompat_def using in1 stackOver Some stackLoc by (cases tIn; fastforce)
              then have McOld:"MCon struct (Memory st) x3" using 6(2) unfolding TypeSafe_def typeCompat_def using in1 stackOver Some stackLoc KMemPtr by (cases tIn; fastforce)
              then have "\<exists>x i. accessStore x3 (Memory st) = Some x \<or> accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some x" using MCon_imps_Some by blast
              moreover have "lessThanTopLocs (Memory st)"using 6(2) unfolding TypeSafe_def by auto
              ultimately obtain tloc where tlocDef: "(tloc<Toploc (Memory st) \<and> LSubPrefL2 x3 (ShowL\<^sub>n\<^sub>a\<^sub>t tloc))"
                by (meson lessThanTopLocs_def MemLSubPrefL2_specific_imps_general)

              have "(\<forall>locs tp.
      accessTypeStore locs (Memory st) = Some tp \<longrightarrow>
      (case accessStore locs (Memory st) of None \<Rightarrow> False
       | Some (MValue v) \<Rightarrow> \<exists>val. MCon tp (Memory st) locs \<and> tp = MTValue val \<and> accessTypeStore locs (Memory st) = Some tp
       | Some (MPointer p) \<Rightarrow> \<exists>len arr. MCon tp (Memory st) p \<and> tp = MTArray len arr
\<and> (\<forall>i<len. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr)))"
                using 6(2) unfolding TypeSafe_def subPrefixStructuralConsistency_def using McOld by auto
              have IH1Link:"(\<forall>locs tp.
       accessTypeStore locs (Memory st') = Some tp \<longrightarrow>
       (case accessStore locs (Memory st') of None \<Rightarrow> False
        | Some (MValue v) \<Rightarrow> \<exists>val. MCon tp (Memory st') locs \<and> tp = MTValue val \<and> accessTypeStore locs (Memory st') = Some tp
        | Some (MPointer p) \<Rightarrow> \<exists>len arr. MCon tp (Memory st') p \<and> tp = MTArray len arr
\<and> (\<forall>i<len. accessTypeStore (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr)))"
                using IH1 cc20 unfolding TypeSafe_def subPrefixStructuralConsistency_def by presburger
              have mlFinalLink:"(\<forall>locs t. accessTypeStore locs (m\<^sub>l) = Some t \<longrightarrow> accessTypeStore locs (Memory st') = Some t)"
                using IH1 cc20 by simp
              have linkS:"(\<forall>i loc. i < Toploc (Memory sgas) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<longrightarrow>
                      accessStore loc (Memory sgas) = accessStore loc m\<^sub>l
                    \<and> accessTypeStore loc (Memory sgas) = accessTypeStore loc m\<^sub>l)"
                using link unfolding ncpOMemInDMem_def by blast
              then have oldLoadedLink:"accessStore x3 (Memory st) = accessStore x3 m\<^sub>l
                    \<and> accessTypeStore x3 (Memory st) = accessTypeStore x3 m\<^sub>l" using tlocDef memSGas by simp
              have SameVAccess:"(\<forall>locs v. accessStore locs (m\<^sub>l) = Some (MPointer v) \<longrightarrow> (\<exists>v'. accessStore locs (Memory st') = Some (MPointer v'))) \<and>
  (\<forall>locs v. accessStore locs ((m\<^sub>l)) = Some (MValue v) \<longrightarrow> (\<exists>v'. accessStore locs (Memory st') = Some (MValue v')))" using IH1 cc20 by auto
              have "MCon struct (Memory st') x3 "
              proof(cases struct)
                case (MTArray x11 x12)
                then have accTypesOld:"\<forall>i<x11. accessTypeStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some x12"
                  using 6(2) unfolding TypeSafe_def denvalueTypeCorrectness_def
                  using in1 Some stackOver KMemPtr structDef stackLoc by fastforce
                then have oldVals:"(\<forall>i<x11.
                                 case accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) of None \<Rightarrow> False
                                   | Some (MValue val) \<Rightarrow> (case x12 of MTArray l a \<Rightarrow> False | MTValue typ
                                       \<Rightarrow> MCon x12 (Memory st) (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
                                   | Some (MPointer loc2) \<Rightarrow> (case x12 of MTArray len' arr' \<Rightarrow> MCon x12 (Memory st) loc2 | MTValue val \<Rightarrow> False)) \<and>
                                   (\<exists>p. accessStore x3 (Memory st) = Some (MPointer p) \<or> accessStore x3 (Memory st) = None)"
                  using McOld MCon.simps(2)[of x11 x12 "Memory st" x3] MTArray by simp
                have "\<forall>i<x11. case accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') of None \<Rightarrow> False
                             | Some (MValue val) \<Rightarrow> (case x12 of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon
                                 x12 (Memory st') (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
                             | Some (MPointer loc2) \<Rightarrow> (case x12 of MTArray len' arr' \<Rightarrow> MCon x12 (Memory st') loc2 | MTValue val \<Rightarrow> False)"
                proof intros
                  fix i
                  assume in1:"i<x11"

                  then consider (ptr) p x11' x12' where "accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some (MPointer p)
                                                  \<and> x12 = MTArray x11' x12'"
                    | (val) v vt where "accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some (MValue v)
                                    \<and> x12 = MTValue vt" using oldVals
                    by (metis MCon.simps(2) MTArray McOld mcon_accessStore)
                  then show "case accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') of None \<Rightarrow> False
                        | Some (MValue val) \<Rightarrow> (case x12 of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon x12 (Memory st') (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
                        | Some (MPointer loc2) \<Rightarrow> (case x12 of MTArray len' arr' \<Rightarrow> MCon x12 (Memory st') loc2 | MTValue val \<Rightarrow> False) "
                  proof(cases)
                    case ptr
                    then obtain t where accNew:"accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some (MPointer t)"
                      using linkS tlocDef memSGas SameVAccess
                      by (metis LSubPrefL2_def Not_Sub_More_Specific)
                    have "accessTypeStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some (MTArray x11' x12')"
                      using accTypesOld ptr in1 by simp
                    then have "accessTypeStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some (MTArray x11' x12')"
                      using mlFinalLink linkS tlocDef memSGas Not_Sub_More_Specific LSubPrefL2_def by metis
                    then have "MCon (MTArray x11' x12') (Memory st') t" using IH1Link accNew by fastforce
                    then show ?thesis using accNew ptr MTArray by simp
                  next
                    case val
                    then have accNew:"\<exists>t. accessStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some (MValue t)"
                      using linkS tlocDef memSGas SameVAccess
                      by (metis LSubPrefL2_def Not_Sub_More_Specific)
                    have "accessTypeStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some (MTValue vt)"
                      using accTypesOld val in1 by simp
                    then have "accessTypeStore (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some (MTValue vt)"
                      using mlFinalLink linkS tlocDef memSGas Not_Sub_More_Specific LSubPrefL2_def by metis
                    then have "MCon (MTValue vt) (Memory st') (hash x3 (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using IH1Link accNew by fastforce
                    then show ?thesis using MTArray accNew val by auto
                  qed

                qed
                moreover have "(\<exists>p. accessStore x3 (Memory st') = Some (MPointer p) \<or> accessStore x3 (Memory st') = None)"
                proof -
                  have "\<forall>i loc. i < Toploc m\<^sub>l \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<longrightarrow>
                      accessStore loc m\<^sub>l = None \<longrightarrow> accessStore loc (Memory st') = None" using IH1 cc20 by auto
                  then show ?thesis using oldVals oldLoadedLink SameVAccess tlocDef
                    by (metis dual_order.strict_trans1 link memSGas)
                qed
                ultimately show ?thesis using MTArray McOld by auto
              next
                case (MTValue x2'')
                then have "(case accessStore x3 (Memory st) of None \<Rightarrow> False | Some (MValue t) \<Rightarrow> typeCon x2'' t | Some (MPointer t) \<Rightarrow> False)"
                  using McOld by simp
                then obtain t where accOld:"accessStore x3 (Memory st) = Some (MValue t)" by (auto split:option.splits memoryvalue.splits)
                then have accNew:"\<exists>t. accessStore x3 (Memory st') = Some (MValue t)" using oldLoadedLink SameVAccess by auto
                have "accessTypeStore x3 (Memory st) = Some (MTValue x2'')"
                  using 6(2) unfolding TypeSafe_def denvalueTypeCorrectness_def using in1 Some stackOver KMemPtr structDef MTValue
                  using stackLoc by force
                then have "accessTypeStore x3 (Memory st') = Some (MTValue x2'')" using mlFinalLink oldLoadedLink by auto
                then have "MCon (MTValue x2'') (Memory st') x3" using IH1Link accNew by force
                then show ?thesis using MTValue by simp
              qed


              then show "case tIn of type.Memory struct \<Rightarrow> MCon struct (Memory st') x3 | _ \<Rightarrow> False" using structDef by simp
            next
              fix x4 assume KStoPtr:"x2 = KStoptr x4"

              then have accO:"accessStore x1 (Stack st) = Some( KStoptr x4)"
                using Some 1 by auto
              then obtain struct where structDef: "tIn = type.Storage struct"
                using 6(2) unfolding TypeSafe_def typeCompat_def using Some KStoPtr stackLoc in1 Some SomeOld
                by (cases tIn) fastforce+
              obtain tprnt lprnt where tprntDef: "((type.Storage tprnt, Storeloc lprnt) |\<in>| fmran (Denvalue e) \<and> CompStoType tprnt struct lprnt x4)"
                using 6(4) using accO in1 unfolding fullyInitialised_def
                using stackLoc structDef by blast

              then have "SCon tprnt lprnt (Storage st'' (Address e))"
                using IH1 unfolding StateInvariant_def TypeSafe_def safeContract_def
                using cx a44 a45
                by (metis (mono_tags, lifting) "6.prems"(3) fi_denvalue_storeloc_to_contract_var fullyInitialised_def)

              then have "SCon struct x4 (Storage st'' (Address e))"
                using tprntDef SCon_imps_sublocs by blast
              then show "case tIn of type.Storage struct \<Rightarrow> SCon struct x4 (Storage st' (Address e)) | _ \<Rightarrow> False "
                using IH1 cc20 stackLoc stackOver in1 Some SomeOld structDef by simp
            qed
          qed
        next
          fix x2 assume storeLoc:"lIn = Storeloc x2"
          then obtain struct where structDef: "tIn = type.Storage struct"
            using 6(2) unfolding TypeSafe_def typeCompat_def using in1
            by (cases tIn) fastforce+
          obtain tprnt lprnt where tprntDef: "((type.Storage tprnt, Storeloc lprnt) |\<in>| fmran (Denvalue e) \<and> CompStoType tprnt struct lprnt x2)"
            using 6(4) using in1 unfolding fullyInitialised_def
            using structDef
            using CompStoType_sameLocNdTyp storeLoc by auto

          then have "SCon tprnt lprnt (Storage st'' (Address e))"
            using IH1 unfolding StateInvariant_def TypeSafe_def safeContract_def
            using cx a44 a45
            by (metis (mono_tags, lifting) "6.prems"(3) fi_denvalue_storeloc_to_contract_var fullyInitialised_def)


          then have "SCon struct x2 (Storage st'' (Address e))"
            using tprntDef SCon_imps_sublocs by blast
          then show "case tIn of type.Storage struct \<Rightarrow> SCon struct x2 (Storage st' (Address e)) | _ \<Rightarrow> False "
            using IH1 cc20 storeLoc stackOver in1 structDef by simp
        qed
      qed
    next
      show "fullyInitialised e (Accounts st') (Stack st') " using 6(4) 1(6) cc20 unfolding fullyInitialised_def
        using IH1 \<open>Address e\<^sub>l = Address e\<close> a45 fullyInitialised_def by auto
    next
      show "denvalueTypeCorrectness e (Stack st') (Memory st')" unfolding denvalueTypeCorrectness_def
      proof intros
        fix t l ptr_loc sub_loc
        assume in1:"(type.Memory t, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l (Stack st') = Some (KMemptr ptr_loc)"
        then have "accessStore l (Stack st) = Some (KMemptr ptr_loc)" using 1 by simp

        have "(\<forall>tp' locs p i.
       (type.Memory tp', Stackloc locs) |\<in>| fmran (Denvalue e\<^sub>l) \<and> accessStore locs k\<^sub>l = Some (KMemptr p) \<and> i <
           Toploc (Memory sgas) \<and> LSubPrefL2 p (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<longrightarrow>
       (\<exists>tp'' loc2 p'.
           (type.Memory tp'', Stackloc loc2) |\<in>| fmran (Denvalue e) \<and>
           accessStore loc2 (Stack sgas) = Some (KMemptr p') \<and>
           (p' = p \<and> tp'' = tp' \<or> (\<exists>len arr. p' \<noteq> p \<and> tp'' = MTArray len arr \<and> CompMemType (Memory sgas) len arr tp' p' p))))"
          using link unfolding ncpDenvalueLimit_def by blast
        have "(\<forall>t l ptr_loc sub_loc.
       (type.Memory t, Stackloc l) |\<in>| fmran (Denvalue e\<^sub>l) \<and> accessStore l (Stack st'') = Some (KMemptr ptr_loc) \<longrightarrow>
       (case t of
        MTArray len arr \<Rightarrow>
          (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st'') = Some arr)
        | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st'') = Some (MTValue val)))"
          using IH1 unfolding TypeSafe_def denvalueTypeCorrectness_def by blast
        have "(case t of MTArray len arr \<Rightarrow> \<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st) = Some arr
       | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st) = Some (MTValue val))"
          using 6(2) in1 1 unfolding TypeSafe_def denvalueTypeCorrectness_def by simp
        then show "case t of
       MTArray len arr \<Rightarrow>
         (\<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr)
       | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st') = Some (MTValue val)"
          using IH1 memSGas typeMstML cc20 by (cases t; simp)
      qed
    next
      show "SomeValSomeTyp (Memory st')"
        using IH1 TypeSafe_def cc20 by auto
    next
      show "subPrefixStructuralConsistency (Memory st')" using IH1 TypeSafe_def cc20 by simp
    next
      show "\<And>locs t. accessTypeStore locs (Memory st) = Some t \<Longrightarrow> accessTypeStore locs (Memory st') = Some t "
        using IH1 cc20 typeMstML memSGas by auto
    next
      fix locs v
      assume in1:"accessStore locs (Memory st) = Some (MPointer v)"
      then have "\<exists>i. i < Toploc (Memory sgas) \<and> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t i)"
        using memSGas 6(2) unfolding TypeSafe_def lessThanTopLocs_def by auto
      then have "accessStore locs (m\<^sub>l) = Some (MPointer v)"
        using in1 link memSGas unfolding ncpOMemInDMem_def by auto
      then show " \<exists>v'. accessStore locs (Memory st') = Some (MPointer v')"
        using IH1 cc20 by simp
    next
      fix locs v
      assume in1:"accessStore locs (Memory st) = Some (MValue v)"
      then have "\<exists>i. i < Toploc (Memory sgas) \<and> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t i)"
        using memSGas 6(2) unfolding TypeSafe_def lessThanTopLocs_def by auto
      then have "accessStore locs (m\<^sub>l) = Some (MValue v)"
        using in1 link memSGas unfolding ncpOMemInDMem_def by auto
      then show " \<exists>v'. accessStore locs (Memory st') = Some (MValue v')"
        using IH1 cc20 by simp
    next
      fix i loc
      assume in1:"i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) "
        and in2:"accessStore loc (Memory st) = None"
      then have "accessStore loc (m\<^sub>l) = None"
        using in1 link memSGas unfolding ncpOMemInDMem_def by auto
      moreover have "i < Toploc (Memory (st\<lparr>Gas := g, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)"
        using in1 link memSGas by simp
      ultimately show "accessStore loc (Memory st') = None"
        using IH1 cc20 by auto
    next
      show "Toploc (Memory st) \<le> Toploc (Memory st')" using memSGas link IH1 cc20 by simp
    qed
  qed
next
  case (7 ad i xe val e cd st)
  show ?case
  proof(cases rule:external[OF 7(4)])
    case (1 adv c g ct cn fb' v t g' v' fp f e\<^sub>l cd\<^sub>l k\<^sub>l m\<^sub>l g'' acc st'')
    then obtain cc :: environment where ccDef: "c = Contract cc"
      by (metis Environment.select_convs(2))

    then have a5:"assert Gas (\<lambda>st. costs (EXTERNAL ad i xe val) e cd st < state.Gas st) st = Normal ((), st)" using 1 by simp
    then obtain sgas where *:"sgas = st\<lparr>Gas := state.Gas st - costs (EXTERNAL ad i xe val) e cd st\<rparr>" by simp
    then have a6:"modify (\<lambda>st. st\<lparr>Gas := state.Gas st - costs (EXTERNAL ad i xe val) e cd st\<rparr>) st = Normal ((), sgas)" by simp
    obtain expGas where a10:" toState (local.expr ad e cd) sgas = Normal ((KValue adv, Value TAddr), expGas)" using 1(2) a6 * by simp
    then have a20:"(case (KValue adv, Value TAddr) of (KValue adv, Value TAddr) \<Rightarrow> return adv | (KValue adv, Value _) \<Rightarrow> throw Err
                    | (KValue adv, _) \<Rightarrow> throw Err | (_, b) \<Rightarrow> throw Err) expGas =
    Normal (adv, expGas)" by simp
    then obtain vd where a30:"assert Err (\<lambda>_. adv \<noteq> Address e) expGas = Normal (vd, expGas)" using 1 by simp
    then have a40:"(case Type (Accounts expGas adv) of None \<Rightarrow> throw Err expGas
                | Some EOA \<Rightarrow> throw Err expGas
                | Some (atype.Contract c) \<Rightarrow> return c expGas) = Normal (c, expGas)" using 1 a10 * by auto
    then have a50:"option Err (\<lambda>_. ep $$ c) expGas = Normal ((ct, cn, fb'), expGas)" using 1 by simp
    then have a60:"toState (local.expr val e cd) expGas = Normal ((KValue v, Value t), expGas\<lparr>Gas := g'\<rparr>)" using 1 a10 * by auto
    then have a70:"(case (KValue v, Value t) of (KValue v, Value t) \<Rightarrow> return (v, t)
                    | (KValue v, _) \<Rightarrow> throw Err
                    | (_, b) \<Rightarrow> throw Err) (expGas\<lparr>Gas := g'\<rparr>) = Normal ((v,t), expGas\<lparr>Gas := g'\<rparr>)" using 1 a10 * by simp
    then have a80:"option Err (\<lambda>_. convert t (TUInt b256) v) (expGas\<lparr>Gas := g'\<rparr>) = Normal (v', expGas\<lparr>Gas := g'\<rparr>)" using 1 by simp
    then obtain loaded where a90:"loaded = ffold_init ct (emptyEnv adv c (Address e) v') (fmdom ct)" using 1(9) by blast
    then have a100:"toState (local.load True fp xe loaded emptyTypedStore emptyStore emptyTypedStore e cd) (expGas\<lparr>Gas := g'\<rparr>)
        = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), expGas\<lparr>Gas := g''\<rparr>)"
      using 1 * a10 by auto
    then have a110:"option Err (\<lambda>st. transfer (Address e) adv v' (Accounts st)) (expGas\<lparr>Gas := g''\<rparr>) = Normal (acc, expGas\<lparr>Gas := g''\<rparr>)"
      using 1 * a10 by auto
    then have a120:"modify (\<lambda>st. st\<lparr>Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>) (expGas\<lparr>Gas :=
        g''\<rparr>) = Normal ((), (expGas\<lparr>Gas := g'', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>))"
      using 1 * a10 by auto

    have contractLoaded:"Contract e\<^sub>l = c" using a90 a100
      using "1"(9) emptyEnv_members ffold_init_contract msel_ssel_expr_load_rexp_gas(4) by presburger
    have addressLoaded: "Address e\<^sub>l = Address loaded" using a90 a100
      using "1"(9) ffold_init_def msel_ssel_expr_load_rexp_gas(4) by presburger

    have tsInitAcc:"\<forall>x y. TypeSafe loaded acc emptyStore emptyTypedStore (Storage st) emptyTypedStore \<and>
       (Denvalue loaded $$ x = Some y \<longrightarrow> snd y = Storeloc x) \<and> (Denvalue loaded $$ x = Some y \<longrightarrow>
           (\<exists>t1. ct $$ x = Some (Var t1) \<and> fst y = type.Storage t1))"
    proof -
      have sc:"safeContract acc (Storage st)"
        using 7(3) 1(10) transfer_type_same unfolding TypeSafe_def safeContract_def by fastforce
      have svv':"svalueTypes v'" unfolding svalueTypes_def
        using 1(6,7) 7(3) 7(5)
        using exprTypeconInduct(3)[of val e cd "(st\<lparr>Gas := g\<rparr>)" g "KValue v" "Value t" g']
          typeSafeConvert[of t v "(TUInt b256)"] convertSame by auto
      have bt:"balanceTypes acc" using 1(10) unfolding balanceTypes_def
      proof -
        have old:"balanceTypes (Accounts (st\<lparr>Gas := g''\<rparr>))" using 7(3) unfolding TypeSafe_def by simp
        have accExp:"(case subBalance (Address e) v' (Accounts (st\<lparr>Gas := g''\<rparr>)) of None \<Rightarrow> None | Some x \<Rightarrow> addBalance adv v' x) = Some acc"
          using 1(10) unfolding transfer_def by blast
        have v'TC: "typeCon (TUInt b256) v'"
          using svv' unfolding svalueTypes_def by blast

        show "\<forall>adv'. typeCon (TUInt b256) (Bal (acc adv')) "
        proof
          fix adv'
          show "typeCon (TUInt b256) (Bal (acc adv')) "
          proof(cases "adv' = (Address e)")
            case True
            then have ns:"adv' \<noteq> adv" using 1 by blast
            then have tco:"typeCon (TUInt b256) (Bal ((Accounts (st\<lparr>Gas := g''\<rparr>)) adv'))"
              using True old accExp balanceTypes_def by blast
            have "Bal (acc (Address e)) = ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts (st\<lparr>Gas :=
                g''\<rparr>) (Address e))) - (ReadL\<^sub>i\<^sub>n\<^sub>t v'))"
              using transfer_subRead[OF 1(10) _ v'TC ] True ns tco by auto
            then show ?thesis using True
              by (metis transfer_Bal_typeCon[unfolded transfer_def, OF accExp] old[unfolded balanceTypes_def])
          next
            case False
            then show ?thesis
            proof(cases "adv' = adv")
              case True
              then have "typeCon (TUInt b256) (Bal (Accounts (st\<lparr>Gas := g''\<rparr>) adv))"
                using True old accExp balanceTypes_def by simp
              then have "Bal (acc adv) = (ShowL\<^sub>i\<^sub>n\<^sub>t ((ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts (st\<lparr>Gas := g''\<rparr>) adv))) + (ReadL\<^sub>i\<^sub>n\<^sub>t v')))"
                using transfer_addRead[OF 1(10)_ v'TC ] 1(3) by blast
              then show ?thesis using True
                using "1"(10,3) Read_ShowL_id \<open>typeCon (TUInt b256) (Bal (Accounts (st\<lparr>Gas := g''\<rparr>) adv))\<close> checkUInt_def transfer_val1 transfer_val2 by auto
            next
              case f2:False
              then show ?thesis using False transfer_eq[OF 1(10)] old
                using balanceTypes_def by force
            qed
          qed
        qed
      qed

      have ltp:"lessThanTopLocs emptyTypedStore" using typedEmptyTopLocs by simp
      have tp:"ep $$ Contract cc = Some (ct, cn, fb')" using ccDef 1(5) by simp
      have af1:"addressFormat adv" using 7(3) unfolding TypeSafe_def AddressTypes_def using 1 by (simp split:option.splits atype.splits)
      have af2:"addressFormat (Address e)" using 7(3) unfolding TypeSafe_def AddressTypes_def using 1 by simp
      have af3:"AddressTypes acc" using 1(10) transfer_type_same 7(3) unfolding TypeSafe_def unfolding AddressTypes_def by simp
      have tcAdvAcc:"Type (acc adv) = Some (atype.Contract (Contract cc))"
        using 1(10) a10 * a40 ccDef transfer_type_same by (auto split:option.splits atype.splits result.splits)
      have svt:"SomeValSomeTyp emptyTypedStore" unfolding SomeValSomeTyp_def accessStore_def accessTypeStore_def emptyTypedStore_def by auto
      have sp:"subPrefixStructuralConsistency emptyTypedStore" unfolding subPrefixStructuralConsistency_def accessTypeStore_def emptyTypedStore_def by simp
      then have " ffold (init ct) (emptyEnv adv (Contract cc) (Address e) v') (fmdom ct) = loaded" using a90 unfolding ffold_init_def using ccDef by simp
      then show ?thesis
        using ffoldInitTypeSafe[OF sc bt svv' ltp tp af1 af2 af3 sp svt tcAdvAcc,of "(fmdom ct)"] by simp
    qed

    have tsInit:"\<forall>x y. TypeSafe loaded (Accounts st) emptyStore emptyTypedStore (Storage st) emptyTypedStore \<and>
       (Denvalue loaded $$ x = Some y \<longrightarrow> snd y = Storeloc x) \<and> (Denvalue loaded $$ x = Some y \<longrightarrow>
           (\<exists>t1. ct $$ x = Some (Var t1) \<and> fst y = type.Storage t1))"
    proof -
      have "safeContract (Accounts st) (Storage st)" using 7(3) unfolding TypeSafe_def AddressTypes_def using 1 by simp
      moreover have svv':"svalueTypes v'" unfolding svalueTypes_def
        using 1(6,7) 7(3) 7(5)
        using exprTypeconInduct(3)[of val e cd "(st\<lparr>Gas := g\<rparr>)" g "KValue v" "Value t" g']
          typeSafeConvert[of t v "(TUInt b256)"] convertSame by auto
      moreover have "balanceTypes (Accounts st)" using 7(3) unfolding TypeSafe_def by simp
      moreover have "lessThanTopLocs emptyStore" using emptyTopLocs by simp
      moreover have "ep $$ Contract cc = Some (ct, cn, fb')" using ccDef 1(5) by simp
      moreover have "addressFormat adv" using 7(3) unfolding TypeSafe_def AddressTypes_def using 1 by (simp split:option.splits atype.splits)
      moreover have "addressFormat (Sender e)" using 7(3) unfolding TypeSafe_def AddressTypes_def using 1 by simp
      moreover have "AddressTypes (Accounts st)" using 7(3) unfolding TypeSafe_def by simp
      moreover have "SomeValSomeTyp emptyTypedStore" unfolding SomeValSomeTyp_def accessTypeStore_def accessStore_def emptyTypedStore_def by simp
      moreover have sp:"subPrefixStructuralConsistency emptyTypedStore" unfolding subPrefixStructuralConsistency_def accessTypeStore_def emptyTypedStore_def by simp
      moreover have "Type (acc adv) = Some (atype.Contract (Contract cc))"
        using 1(10) a10 * a40 ccDef transfer_type_same by (auto split:option.splits atype.splits result.splits)

      ultimately show ?thesis
        using a90 ccDef unfolding ffold_init_def
        using ffoldInitTypeSafe[of acc "Storage st" v' emptyTypedStore cc ct "(cn,fb')" adv _ " (fmdom ct)"]
        using TypeSafe_def tsInitAcc by presburger
    qed

    have contractL:"Contract loaded = c" using a90 by simp
    have addressL:"Address loaded = adv" using a90 by simp
    have fi1:"(\<exists>c. Type (Accounts (st\<lparr>Gas := g'\<rparr>) (Address loaded)) = Some (atype.Contract c) \<and> Contract loaded = c)" using contractL addressL 1 a10 * a40 by simp
    have "\<exists>dud. ep $$ Contract loaded = Some (ct, dud)" using a50 contractL 1 a10 * by blast
    moreover have "\<forall>id v. (ct $$ id = Some (Var v)) = (Denvalue loaded $$ id = Some (type.Storage v, Storeloc id))"
      using a90 unfolding ffold_init_def using ffoldInit_var_storage_mapping_eq[of ct adv c "Address e" v' loaded] by blast


    have "Type (Accounts (expGas\<lparr>Gas := g'', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>) (Address e\<^sub>l)) =
        Type (Accounts (st\<lparr>Gas := g'\<rparr>) (Address loaded))"
      using addressLoaded 1(10) a10 * transfer_type_same by simp
    then have fi3:"(\<exists>c. Type (Accounts (expGas\<lparr>Gas := g'', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)
        (Address e\<^sub>l)) = Some (atype.Contract c) \<and> Contract e\<^sub>l = c)"
      using contractLoaded fi1
      using contractL by presburger


    then have tsLoaded:"TypeSafe e\<^sub>l (Accounts (st\<lparr>Gas := g'\<rparr>)) k\<^sub>l m\<^sub>l (Storage (st\<lparr>Gas := g'\<rparr>)) cd\<^sub>l \<and>
    fullyInitialised e\<^sub>l (Accounts (st\<lparr>Gas := g'\<rparr>)) k\<^sub>l"
    proof -
      have ld:"load True fp xe loaded emptyTypedStore emptyStore emptyTypedStore e cd (st\<lparr>Gas := g'\<rparr>) g' = Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), g'')" using 1
        using a90 ffold_init_def by presburger

      have "fullyInitialised loaded (Accounts (st\<lparr>Gas := g'\<rparr>)) emptyStore"
      proof -
        obtain c_fi where cfi:
          "Type (Accounts (st\<lparr>Gas := g'\<rparr>) (Address loaded)) = Some (atype.Contract c_fi) \<and> Contract loaded = c_fi"
          using fi1 by blast
        obtain dud_fi where epfi:"ep $$ Contract loaded = Some (ct, dud_fi)"
          using a50 contractL 1 a10 * by blast
        have mapfi:"\<forall>id v. (ct $$ id = Some (Var v)) = (Denvalue loaded $$ id = Some (type.Storage v, Storeloc id))"
          using a90 unfolding ffold_init_def using ffoldInit_var_storage_mapping_eq[of ct adv c "Address e" v' loaded]
          by blast
        have locfi:"\<forall>id v loc. Denvalue loaded $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc"
        proof (intro allI impI)
          fix id v loc
          assume h:"Denvalue loaded $$ id = Some (type.Storage v, Storeloc loc)"
          have hloc:"Denvalue loaded $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> snd (type.Storage v, Storeloc loc) = Storeloc id"
            using tsInit by blast
          then show "id = loc" using h by simp
        qed
        have ptrfi:"\<forall>t l p.
            (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue loaded) \<and> accessStore l emptyStore = Some (KStoptr p) \<longrightarrow>
            (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue loaded) \<and> CompStoType t' t l' p)"
          by (simp add: accessStore_def emptyStore_def)
        show ?thesis using cfi epfi mapfi locfi ptrfi
          using fullyInitialised_def by blast
      qed
      then show ?thesis
        using * 1(9) 7(3) tsInit 7(5) using fi1 ld
        using exprTypeconInduct(4)[of True fp xe loaded emptyTypedStore emptyStore emptyTypedStore e cd "(st\<lparr>Gas := g'\<rparr>)" g' e\<^sub>l cd\<^sub>l k\<^sub>l m\<^sub>l g'']
        by simp
    qed


    then have ts1:"TypeSafe e\<^sub>l (Accounts (expGas\<lparr>Gas :=
        g'', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)) (Stack (expGas\<lparr>Gas := g'', Accounts := acc, Stack :=
        k\<^sub>l, Memory := m\<^sub>l\<rparr>))
     (Memory (expGas\<lparr>Gas :=
         g'', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)) (Storage (expGas\<lparr>Gas := g'', Accounts := acc, Stack
         := k\<^sub>l, Memory := m\<^sub>l\<rparr>)) cd\<^sub>l"
      using tsInitAcc a10 * 1 unfolding TypeSafe_def by auto

    have fiFinal:"fullyInitialised e\<^sub>l (Accounts(expGas\<lparr>Gas :=
        g'', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)) (Stack (expGas\<lparr>Gas := g'', Accounts := acc, Stack :=
        k\<^sub>l, Memory := m\<^sub>l\<rparr>))"
    proof -
      from tsLoaded obtain c_fi ct_fi dud_fi where fiOld:"
           Type (Accounts (st\<lparr>Gas := g'\<rparr>) (Address e\<^sub>l)) = Some (atype.Contract c_fi) \<and>
           Contract e\<^sub>l = c_fi \<and>
           ep $$ c_fi = Some (ct_fi, dud_fi) \<and>
           (\<forall>id v. (ct_fi $$ id = Some (Var v)) = (Denvalue e\<^sub>l $$ id = Some (type.Storage v, Storeloc id))) \<and>
           (\<forall>id v loc. Denvalue e\<^sub>l $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc) \<and>
           (\<forall>t l p.
               (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e\<^sub>l) \<and> accessStore l k\<^sub>l = Some (KStoptr p) \<longrightarrow>
               (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e\<^sub>l) \<and> CompStoType t' t l' p))"
        unfolding fullyInitialised_def by blast
      have typeNew:"Type (Accounts (expGas\<lparr>Gas := g'', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>) (Address e\<^sub>l))
              = Some (atype.Contract c_fi)"
        using fiOld addressLoaded
          \<open>Type (Accounts (expGas\<lparr>Gas := g'', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>) (Address
              e\<^sub>l)) = Type (Accounts (st\<lparr>Gas := g'\<rparr>) (Address loaded))\<close>
        by simp
      have ptrNew:"\<forall>t l p.
        (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e\<^sub>l) \<and>
        accessStore l (Stack (expGas\<lparr>Gas := g'', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)) = Some (KStoptr p) \<longrightarrow>
        (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e\<^sub>l) \<and> CompStoType t' t l' p)"
        using fiOld by simp
      show ?thesis
        unfolding fullyInitialised_def using fiOld typeNew ptrNew by blast
    qed

    then have IH1:"StateInvariant e\<^sub>l (expGas\<lparr>Gas := g'', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>) st'' cd\<^sub>l"
      using 7(1)[OF a5 a6 a10 a20 a30 a40 a50 _ _ a60 a70 _ a80 a90 1(8) _ _ _ _ a100 _ _ _ a110 _ _ a120 ts1
          ] 1(11) 1(2) a10 * by fastforce

    have accFinal:"Accounts st' = Accounts st''" using 1 by simp
    have storageFinal:"Storage st' = Storage st''" using 1 by simp

    have SafeC:"safeContract (Accounts st'') (Storage st'')" using IH1 unfolding StateInvariant_def TypeSafe_def by blast
    then have "Storage st'' = Storage st'" using 1 by auto
    then have scNew:"\<forall>e ct dud i tp. Type (Accounts
        st'' (Address e)) = Some (atype.Contract (environment.Contract e)) \<and> ep $$ Contract (e::environment) = Some (ct, dud) \<and>
            ct $$ i = Some (Var tp) \<longrightarrow> SCon tp i (Storage st'' (Address e))"
      using SafeC unfolding safeContract_def by simp
    have acc:"(\<forall>adv. case Type (Accounts st adv) of None \<Rightarrow> True | Some EOA \<Rightarrow> True | Some (atype.Contract c) \<Rightarrow> addressFormat adv \<and> c |\<in>| fmdom ep)"
      using 7(3) unfolding TypeSafe_def AddressTypes_def by blast
    obtain cOld where "Type (Accounts st (Address e)) = Some (atype.Contract cOld) \<and> Contract e = cOld"
      using 7(5) unfolding fullyInitialised_def by simp
    then obtain ctO dudO where ctoDef: "ep $$ Contract e = Some (ctO, dudO)" using acc
      using "7.prems"(3) typesafe_base.fullyInitialised_def typesafe_base_axioms by blast
    have fi2:"\<forall>id v. (ctO $$ id = Some (Var v)) = (Denvalue e $$ id = Some (type.Storage v, Storeloc id))"
      using 7(5) ctoDef unfolding fullyInitialised_def by auto
    have fiLoc:"\<forall>id v loc. Denvalue e $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc"
      using 7(5) unfolding fullyInitialised_def by blast

    show ?thesis unfolding StateInvariant_def
    proof intros
      show "TypeSafe e (Accounts st') (Stack st') (Memory st') (Storage st') cd" unfolding TypeSafe_def
      proof intros
        show "AddressTypes (Accounts st')" using IH1 unfolding StateInvariant_def TypeSafe_def using 1(12) by simp
      next
        show "safeContract (Accounts st') (Storage st')" using IH1 storageFinal 1 unfolding StateInvariant_def TypeSafe_def by auto
      next
        show "unique_locations (Denvalue e)" using "7.prems"(1) typeSafeUnique by blast
      next
        have old:" compPointers (Stack st'') (Denvalue e\<^sub>l)"
          using IH1 unfolding StateInvariant_def TypeSafe_def by blast
        show "compPointers (Stack st') (Denvalue e)" unfolding compPointers_def
        proof intros
          fix tp1 tp2 l1 l2 l1' l2' stl1 stl2
          assume a0:"(type.Storage tp1, l1) |\<in>| fmran (Denvalue e) \<and>
       (type.Storage tp2, l2) |\<in>| fmran (Denvalue e) \<and>
       (l1 = Stackloc l1' \<and> accessStore l1' (Stack st') = Some (KStoptr stl1) \<or> l1 = Storeloc stl1) \<and>
       (l2 = Stackloc l2' \<and> accessStore l2' (Stack st') = Some (KStoptr stl2) \<or> l2 = Storeloc stl2)"
          then have a5:"accessStore l1' (Stack st') = accessStore l1' (Stack st)" using 1 by simp
          have a10:"accessStore l2' (Stack st') = accessStore l2' (Stack st)" using 1 by auto
          show "if TypedStoSubpref stl2 stl1 tp1 then CompStoType tp1 tp2 stl1 stl2
                else if TypedStoSubpref stl1 stl2 tp2 then CompStoType tp2 tp1 stl2 stl1 else True"
            using 7(3) unfolding TypeSafe_def compPointers_def using a0 a5 a10 by simp
        qed
      next
        show "balanceTypes (Accounts st')" using accFinal IH1 unfolding StateInvariant_def TypeSafe_def by auto
      next
        have "envAddressesWellFormed e" using "7.prems"(1) unfolding TypeSafe_def by simp
        then show "addressFormat (Address e)" and "addressFormat (Sender e)" by simp+
      next
        show "svalueTypes (Svalue e)" using "7.prems"(1) unfolding TypeSafe_def by simp
      next
        show "lessThanTopLocs (Stack st')" using 1(12) "7.prems"(1) unfolding TypeSafe_def by simp
      next
        show "lessThanTopLocs cd" using "7.prems"(1) unfolding TypeSafe_def by simp
      next
        show "lessThanTopLocs (Memory st')" using 1(12) "7.prems"(1) unfolding TypeSafe_def by simp
      next
        show "typeCompat (Denvalue e) (Stack st') (Memory st') (Storage st' (Address e)) cd"
          unfolding typeCompat_def
        proof intros
          fix t l
          assume tc1:"(t, l) |\<in>| fmran (Denvalue e)"
          show "denvalueCon (Stack st') (Memory st') (Storage st' (Address e)) cd t l"
          proof(cases l)
            case (Stackloc x1)
            then show ?thesis
            proof(cases "accessStore x1 (Stack st')")
              case None
              then show ?thesis using tc1 Stackloc using 7(3) 1(12) unfolding TypeSafe_def typeCompat_def by force
            next
              case (Some a)
              then show ?thesis
              proof(cases a)
                case (KValue x1)
                then show ?thesis apply(cases t) using tc1 Stackloc Some using 7(3) 1(12) unfolding TypeSafe_def typeCompat_def by force+
              next
                case (KCDptr x2)
                then show ?thesis apply(cases t) using tc1 Stackloc Some using 7(3) 1(12) unfolding TypeSafe_def typeCompat_def by force+
              next
                case (KMemptr x3)
                then show ?thesis apply(cases t) using tc1 Stackloc Some using 7(3) 1(12) unfolding TypeSafe_def typeCompat_def by force+
              next
                case (KStoptr x4)
                then have accO:"accessStore x1 (Stack st) = Some( KStoptr x4)"
                  using Some 1 by auto
                then obtain struct where structDef: "t = type.Storage struct"
                  using 7(3) unfolding TypeSafe_def typeCompat_def using tc1 Some KStoptr Stackloc
                  by (cases t) fastforce+
                obtain tprnt lprnt where tprntDef: "((type.Storage tprnt, Storeloc lprnt) |\<in>| fmran (Denvalue e) \<and> CompStoType tprnt struct lprnt x4)"
                  using 7(5) using accO tc1 unfolding fullyInitialised_def
                  using Stackloc structDef by blast

                then have "SCon tprnt lprnt (Storage st'' (Address e))"
                proof -
                  from tprntDef obtain kpr where kprDef:"Denvalue e $$ kpr = Some (type.Storage tprnt, Storeloc lprnt)"
                    using fmlookup_ran_iff by blast
                  have "kpr = lprnt" using fiLoc kprDef by blast
                  hence denL:"Denvalue e $$ lprnt = Some (type.Storage tprnt, Storeloc lprnt)" using kprDef by simp
                  have "ctO $$ lprnt = Some (Var tprnt)" using fi2 denL by blast
                  moreover have typeEFinal:"Type (Accounts st'' (Address e)) = Some (atype.Contract (Contract e))"
                    using 7(5) atype_same "7.prems"(2,3) unfolding fullyInitialised_def
                    by (metis accFinal)
                  ultimately show ?thesis using scNew ctoDef by blast
                qed
                then have "SCon struct x4 (Storage st'' (Address e))"
                  using tprntDef SCon_imps_sublocs by blast
                then show ?thesis using Stackloc Some KStoptr structDef storageFinal by simp
              qed
            qed
          next
            case (Storeloc x2)
            then obtain struct where structDef: "t = type.Storage struct"
              using 7(3) tc1 unfolding TypeSafe_def typeCompat_def by (cases t,fastforce+)

            then have "SCon struct x2 (Storage st'' (Address e))"
            proof -
              have inRan:"(type.Storage struct, Storeloc x2) |\<in>| fmran (Denvalue e)"
                using tc1 Storeloc structDef by simp
              then obtain kpr where kprDef:"Denvalue e $$ kpr = Some (type.Storage struct, Storeloc x2)"
                using fmlookup_ran_iff by metis
              have "kpr = x2" using fiLoc kprDef by blast
              hence denX2:"Denvalue e $$ x2 = Some (type.Storage struct, Storeloc x2)" using kprDef by simp
              have "ctO $$ x2 = Some (Var struct)" using fi2 denX2 by blast
              moreover have typeEFinal:"Type (Accounts st'' (Address e)) = Some (atype.Contract (Contract e))"
                using 7(5) atype_same "7.prems"(2,3) unfolding fullyInitialised_def
                by (metis accFinal)
              ultimately show ?thesis using scNew ctoDef by blast
            qed
            then show ?thesis using Storeloc structDef
              by (simp add: storageFinal)
          qed
        qed
      next
        show "denvalueTypeCorrectness e (Stack st') (Memory st')" using 7(3) 1(12) unfolding TypeSafe_def by simp
      next
        show "subPrefixStructuralConsistency (Memory st')" using 7(3) 1(12) unfolding TypeSafe_def by simp
      next
        show "SomeValSomeTyp (Memory st')" using 7(3) 1(12) unfolding TypeSafe_def by simp
      qed
    next
      have fiOld:"
        \<exists>c ct dud.
          Type (Accounts st (Address e)) = Some (atype.Contract c) \<and>
          Contract e = c \<and>
          ep $$ c = Some (ct, dud) \<and>
          (\<forall>id v. (ct $$ id = Some (Var v)) = (Denvalue e $$ id = Some (type.Storage v, Storeloc id))) \<and>
          (\<forall>id v loc. Denvalue e $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc) \<and>
          (\<forall>t l p.
              (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l (Stack st) = Some (KStoptr p) \<longrightarrow>
              (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e) \<and> CompStoType t' t l' p))"
        using 7(5) unfolding fullyInitialised_def by blast
      then obtain c_fi ct_fi dud_fi where fiC:"
          Type (Accounts st (Address e)) = Some (atype.Contract c_fi) \<and>
          Contract e = c_fi \<and>
          ep $$ c_fi = Some (ct_fi, dud_fi) \<and>
          (\<forall>id v. (ct_fi $$ id = Some (Var v)) = (Denvalue e $$ id = Some (type.Storage v, Storeloc id))) \<and>
          (\<forall>id v loc. Denvalue e $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc)"
        and fiPtr:"\<forall>t l p.
              (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l (Stack st) = Some (KStoptr p) \<longrightarrow>
              (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e) \<and> CompStoType t' t l' p)"
        by blast
      have typeNew:"Type (Accounts st' (Address e)) = Some (atype.Contract c_fi)"
        using fiC atype_same "7.prems"(2,3) statement_with_gas.atype_same statement_with_gas_axioms by blast
      have ptrNew:"\<forall>t l p.
           (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l (Stack st') = Some (KStoptr p) \<longrightarrow>
           (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e) \<and> CompStoType t' t l' p)"
        using 1 fiFinal 7(5) unfolding fullyInitialised_def by auto
      show "fullyInitialised e (Accounts st') (Stack st')"
        unfolding fullyInitialised_def using fiC fiPtr ptrNew typeNew by blast
    next
      show "\<And>locs t. accessTypeStore locs (Memory st) = Some t \<Longrightarrow> accessTypeStore locs (Memory st') = Some t"
        using 7(3) 1(12) by simp
    next
      show "\<And>locs v.
       accessStore locs (Memory st) = Some (MPointer v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MPointer v')"
        using 1(12) by simp
    next
      show "\<And>locs v. accessStore locs (Memory st) = Some (MValue v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MValue v')"
        using 1(12) by simp
    next
      show "\<And>i loc.
       i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<Longrightarrow>
       accessStore loc (Memory st) = None \<Longrightarrow> accessStore loc (Memory st') = None"
        using 1(12) by simp
    next
      show "Toploc (Memory st) \<le> Toploc (Memory st')" using 1(12) by simp
    qed
  next
    case (2 adv c g ct cn fb' v t g' v' acc st'')
    then obtain cc :: environment where ccDef: "c = Contract cc"
      by (metis Environment.select_convs(2))

    then have a5:"assert Gas (\<lambda>st. costs (EXTERNAL ad i xe val) e cd st < state.Gas st) st = Normal ((), st)" using 2 by simp
    then obtain sgas where *:"sgas = st\<lparr>Gas := state.Gas st - costs (EXTERNAL ad i xe val) e cd st\<rparr>" by simp
    then have a6:"modify (\<lambda>st. st\<lparr>Gas := state.Gas st - costs (EXTERNAL ad i xe val) e cd st\<rparr>) st = Normal ((), sgas)" by simp
    obtain expGas where a10:" toState (local.expr ad e cd) sgas = Normal ((KValue adv, Value TAddr), expGas)" using 2(2) a6 * by simp
    then have a20:"(case (KValue adv, Value TAddr) of (KValue adv, Value TAddr) \<Rightarrow> return adv | (KValue adv, Value _) \<Rightarrow> throw Err
                    | (KValue adv, _) \<Rightarrow> throw Err | (_, b) \<Rightarrow> throw Err) expGas =
    Normal (adv, expGas)" by simp
    then obtain vd where a30:"assert Err (\<lambda>_. adv \<noteq> Address e) expGas = Normal (vd, expGas)" using 2 by simp
    then have a40:"(case Type (Accounts expGas adv) of None \<Rightarrow> throw Err expGas
                | Some EOA \<Rightarrow> throw Err expGas
                | Some (atype.Contract c) \<Rightarrow> return c expGas) = Normal (c, expGas)" using 2 a10 * by auto
    then have a50:"option Err (\<lambda>_. ep $$ c) expGas = Normal ((ct, cn, fb'), expGas)" using 2 by simp
    then have a60:"toState (local.expr val e cd) expGas = Normal ((KValue v, Value t), expGas\<lparr>Gas := g'\<rparr>)" using 2 a10 * by auto
    then have a70:"(case (KValue v, Value t) of (KValue v, Value t) \<Rightarrow> return (v, t)
                    | (KValue v, _) \<Rightarrow> throw Err
                    | (_, b) \<Rightarrow> throw Err) (expGas\<lparr>Gas := g'\<rparr>) = Normal ((v,t), expGas\<lparr>Gas := g'\<rparr>)" using 2 a10 * by simp
    then have a80:"option Err (\<lambda>_. convert t (TUInt b256) v) (expGas\<lparr>Gas := g'\<rparr>) = Normal (v', expGas\<lparr>Gas := g'\<rparr>)" using 2 by simp
    then obtain loaded where a90:"loaded = ffold_init ct (emptyEnv adv c (Address e) v') (fmdom ct)" using 2(9) by blast

    then have a110:"option Err (\<lambda>st. transfer (Address e) adv v' (Accounts st)) (expGas\<lparr>Gas := g'\<rparr>) = Normal (acc, expGas\<lparr>Gas := g'\<rparr>)"
      using 2 * a10 by auto


    have tsInitAcc:"\<forall>x y. TypeSafe loaded acc emptyStore emptyTypedStore (Storage st) emptyTypedStore \<and>
       (Denvalue loaded $$ x = Some y \<longrightarrow> snd y = Storeloc x) \<and> (Denvalue loaded $$ x = Some y \<longrightarrow>
           (\<exists>t1. ct $$ x = Some (Var t1) \<and> fst y = type.Storage t1))"
    proof -
      have "safeContract (Accounts st) (Storage st)" using 7(3) unfolding TypeSafe_def AddressTypes_def using 2 by simp
      moreover have "safeContract acc (state.Storage st)"
        using "2"(9) calculation safeContract_def transfer_type_same by auto
      moreover have svv':"svalueTypes v'" unfolding svalueTypes_def
        using 2(6,7) 7(3) 7(5)
        using exprTypeconInduct(3)[of val e cd "(st\<lparr>Gas := g\<rparr>)" g "KValue v" "Value t" g']
          typeSafeConvert[of t v "(TUInt b256)"] convertSame by auto
      moreover have "balanceTypes acc" using 2(10) unfolding balanceTypes_def
      proof -
        have old:"balanceTypes (Accounts (st\<lparr>Gas := g'\<rparr>))" using 7(3) unfolding TypeSafe_def by simp
        have accExp:"(case subBalance (Address e) v' (Accounts (st)) of None \<Rightarrow> None | Some x \<Rightarrow> addBalance adv v' x) = Some acc"
          using 2(9) unfolding transfer_def by blast
        have v'TC: "typeCon (TUInt b256) v'"
          using svv' unfolding svalueTypes_def by blast

        show "\<forall>adv'. typeCon (TUInt b256) (Bal (acc adv')) "
        proof
          fix adv'
          show "typeCon (TUInt b256) (Bal (acc adv')) "
          proof(cases "adv' = (Address e)")
            case True
            then have ns:"adv' \<noteq> adv" using 2 by blast
            then have tco:"typeCon (TUInt b256) (Bal ((Accounts (st\<lparr>Gas := g'\<rparr>)) adv'))"
              using True old accExp balanceTypes_def by blast
            have "Bal (acc (Address e)) = ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts (st\<lparr>Gas := g'\<rparr>) (Address e))) - (ReadL\<^sub>i\<^sub>n\<^sub>t v'))"
              using transfer_subRead[OF 2(9) _ v'TC ] True ns tco by auto
            then show ?thesis using True

              using "2"(9) Read_ShowL_id checkUInt_def tco transfer_val3 v'TC by fastforce
          next
            case False
            then show ?thesis
            proof(cases "adv' = adv")
              case True
              then have "typeCon (TUInt b256) (Bal (Accounts (st\<lparr>Gas := g'\<rparr>) adv))"
                using True old accExp balanceTypes_def by simp
              then have "Bal (acc adv) = (ShowL\<^sub>i\<^sub>n\<^sub>t ((ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts (st\<lparr>Gas := g'\<rparr>) adv))) + (ReadL\<^sub>i\<^sub>n\<^sub>t v')))"
                using transfer_addRead[OF 2(9)_ v'TC ] 2(3) by auto
              then show ?thesis using True
                using "2"(9,3) Read_ShowL_id \<open>typeCon (TUInt b256) (Bal (Accounts (st\<lparr>Gas := g'\<rparr>) adv))\<close> checkUInt_def transfer_val1 transfer_val2 by auto
            next
              case f2:False
              then show ?thesis using False transfer_eq[OF 2(9)] old
                using balanceTypes_def by force
            qed
          qed
        qed
      qed
      moreover have "lessThanTopLocs emptyStore" using emptyTopLocs by simp
      moreover have "ep $$ Contract cc = Some (ct, cn, fb')" using ccDef 2(5) by simp
      moreover have "addressFormat adv" using 7(3) unfolding TypeSafe_def AddressTypes_def using 2 by (simp split:option.splits atype.splits)
      moreover have "addressFormat (Sender e)" using 7(3) unfolding TypeSafe_def AddressTypes_def using 2 by simp
      moreover have "AddressTypes acc" using 2(9) transfer_type_same 7(3) unfolding TypeSafe_def unfolding AddressTypes_def by simp
      moreover have "addressFormat (Address e)" using "7.prems"(1) unfolding TypeSafe_def by simp
      moreover have "SomeValSomeTyp emptyTypedStore" unfolding SomeValSomeTyp_def accessTypeStore_def accessStore_def
        by (simp add: emptyTypedStore_def)
      moreover have sp:"subPrefixStructuralConsistency emptyTypedStore" unfolding subPrefixStructuralConsistency_def accessTypeStore_def emptyTypedStore_def by simp
      moreover have "Type (acc adv) = Some (atype.Contract (Contract cc))"
        using 2(9) a10 * a40 ccDef transfer_type_same by (auto split:option.splits atype.splits result.splits)

      ultimately show ?thesis
        using a90 ccDef unfolding ffold_init_def using ffoldInitTypeSafe[of acc "Storage st" v' emptyTypedStore cc ct "(cn,fb')" adv "(Address e)" " (fmdom ct)"]
        using typedEmptyTopLocs by blast
    qed

    have contractL:"Contract loaded = c" using a90 by simp
    have addressL:"Address loaded = adv" using a90 by simp
    have fi1:"(\<exists>c. Type (Accounts (st\<lparr>Gas := g'\<rparr>) (Address loaded)) = Some (atype.Contract c) \<and> Contract loaded = c)" using contractL addressL 2 a10 * a40 by simp
    have ct1:"\<exists>dud. ep $$ Contract loaded = Some (ct, dud)" using a50 contractL 2 a10 * by blast
    then have fi2:"\<forall>id v. (Denvalue loaded $$ id = Some (type.Storage v, Storeloc id)) = (ct $$ id = Some (Var v))"
      using a90 unfolding ffold_init_def using ffoldInit_var_storage_mapping_eq[of ct adv c _ v' loaded] by auto
    then have fi3:"(\<exists>c. Type ((acc) (Address loaded)) = Some (atype.Contract c) \<and> Contract loaded = c)"
      using fi1 contractL 2(9) transfer_type_same by simp

    have a120:" TypeSafe loaded (acc) (emptyStore) (emptyTypedStore) (Storage st) emptyTypedStore" using tsInitAcc
      by simp
    moreover have "fullyInitialised loaded (Accounts (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory :=
        emptyTypedStore\<rparr>)) (Stack (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>))"
    proof -
      obtain c_fi where cfi0:"Type (acc (Address loaded)) = Some (atype.Contract c_fi) \<and> Contract loaded = c_fi"
        using fi3 by blast
      have cfi:"Type (Accounts (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>) (Address loaded))
            = Some (atype.Contract c_fi) \<and> Contract loaded = c_fi"
        using cfi0 by simp
      obtain dud_fi where epfi:"ep $$ Contract loaded = Some (ct, dud_fi)"
        using ct1 by blast
      have mapfi:"\<forall>id v. (ct $$ id = Some (Var v)) = (Denvalue loaded $$ id = Some (type.Storage v, Storeloc id))"
        using fi2 by blast
      have locfi:"\<forall>id v loc. Denvalue loaded $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc"
      proof (intro allI impI)
        fix id v loc
        assume h:"Denvalue loaded $$ id = Some (type.Storage v, Storeloc loc)"
        have hloc:"Denvalue loaded $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> snd (type.Storage v, Storeloc loc) = Storeloc id"
          using tsInitAcc by blast
        then show "id = loc" using h by simp
      qed
      have ptrfi:"\<forall>t l p.
          (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue loaded) \<and>
          accessStore l (Stack (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>)) = Some (KStoptr p) \<longrightarrow>
          (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue loaded) \<and> CompStoType t' t l' p)"
        by (simp add: accessStore_def emptyStore_def)
      show ?thesis
        unfolding fullyInitialised_def using cfi epfi mapfi locfi ptrfi by blast
    qed
    ultimately have IH1:"StateInvariant loaded (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>) st'' emptyTypedStore"
      using 7(2)[OF a5 a6 a10 a20 a30 a40 a50 _ _ a60 a70 _ a80 a90 2(8) a110,
          of "(cn, fb')" cn fb' _ _ _ _ _ "(st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>)" st'']
        2(10) 2 * a10 a90 by fastforce

    have accFinal:"Accounts st' = Accounts st''" using 2 by simp
    have storageFinal:"Storage st' = Storage st''" using 2 by simp

    have acc:"(\<forall>adv. case Type (Accounts st adv) of None \<Rightarrow> True | Some EOA \<Rightarrow> True | Some (atype.Contract c) \<Rightarrow> addressFormat adv \<and> c |\<in>| fmdom ep)"
      using 7(3) unfolding TypeSafe_def AddressTypes_def by blast
    obtain cOld where "Type (Accounts st (Address e)) = Some (atype.Contract cOld) \<and>Contract e = cOld"
      using 7(5) unfolding fullyInitialised_def by simp
    then obtain ctO dudO where ctoDef: "ep $$ Contract e = Some (ctO, dudO)" using acc
      using "7.prems"(3) typesafe_base.fullyInitialised_def typesafe_base_axioms by blast
    have SafeC:"safeContract (Accounts st'') (Storage st'')" using IH1 unfolding StateInvariant_def TypeSafe_def by blast

    then have scNew:"\<forall>e ct dud i tp. Type (Accounts
        st'' (Address e)) = Some (atype.Contract (environment.Contract e)) \<and> ep $$ Contract (e::environment) = Some (ct, dud) \<and> ct
            $$ i = Some (Var tp) \<longrightarrow> SCon tp i (Storage st'' (Address e))"
      using SafeC unfolding safeContract_def by simp


    have fi4:"(\<forall>id v. \<exists>dud. ep $$ Contract loaded = Some (ct, dud)
                          \<and> ct $$ id = Some (Var v) = (Denvalue loaded $$ id = Some (type.Storage v, Storeloc id)))"
      using fi1 ct1 fi2
      by presburger
    show ?thesis unfolding StateInvariant_def
    proof intros
      show "TypeSafe e (Accounts st') (Stack st') (Memory st') (Storage st') cd" unfolding TypeSafe_def
      proof intros
        show "AddressTypes (Accounts st')" using IH1 unfolding StateInvariant_def TypeSafe_def using 2 by simp
      next
        show "safeContract (Accounts st') (Storage st')" using IH1 storageFinal 2 unfolding StateInvariant_def TypeSafe_def by auto
      next
        show "unique_locations (Denvalue e)" using "7.prems"(1) typeSafeUnique by blast
      next
        show "compPointers (Stack st') (Denvalue e)" unfolding compPointers_def
        proof intros
          fix tp1 tp2 l1 l2 l1' l2' stl1 stl2
          assume a0:"(type.Storage tp1, l1) |\<in>| fmran (Denvalue e) \<and>
       (type.Storage tp2, l2) |\<in>| fmran (Denvalue e) \<and>
       (l1 = Stackloc l1' \<and> accessStore l1' (Stack st') = Some (KStoptr stl1) \<or> l1 = Storeloc stl1) \<and>
       (l2 = Stackloc l2' \<and> accessStore l2' (Stack st') = Some (KStoptr stl2) \<or> l2 = Storeloc stl2)"
          then have a5:"accessStore l1' (Stack st') = accessStore l1' (Stack st)" using 2 by simp
          have a10:"accessStore l2' (Stack st') = accessStore l2' (Stack st)" using 2 by auto
          show "if TypedStoSubpref stl2 stl1 tp1 then CompStoType tp1 tp2 stl1 stl2
                else if TypedStoSubpref stl1 stl2 tp2 then CompStoType tp2 tp1 stl2 stl1 else True"
            using 7(3) unfolding TypeSafe_def compPointers_def using a0 a5 a10 by simp
        qed
      next
        show "balanceTypes (Accounts st')" using accFinal IH1 unfolding StateInvariant_def TypeSafe_def by auto
      next
        have "envAddressesWellFormed e" using "7.prems"(1) unfolding TypeSafe_def by simp
        then show "addressFormat (Address e)" and "addressFormat (Sender e)" by simp+
      next
        show "svalueTypes (Svalue e)" using "7.prems"(1) unfolding TypeSafe_def by simp
      next
        show "lessThanTopLocs (Stack st')" using 2 "7.prems"(1) unfolding TypeSafe_def by simp
      next
        show "lessThanTopLocs cd" using "7.prems"(1) unfolding TypeSafe_def by simp
      next
        show "lessThanTopLocs (Memory st')" using 2 "7.prems"(1) unfolding TypeSafe_def by simp
      next
        show "typeCompat (Denvalue e) (Stack st') (Memory st') (Storage st' (Address e)) cd"
          unfolding typeCompat_def
        proof intros
          fix t l
          assume tc1:"(t, l) |\<in>| fmran (Denvalue e)"
          show "denvalueCon (Stack st') (Memory st') (Storage st' (Address e)) cd t l"
          proof(cases l)
            case (Stackloc x1)
            then show ?thesis
            proof(cases "accessStore x1 (Stack st')")
              case None
              then show ?thesis using tc1 Stackloc using 7(3) 2 unfolding TypeSafe_def typeCompat_def by force
            next
              case (Some a)
              then show ?thesis
              proof(cases a)
                case (KValue x1)
                then show ?thesis apply(cases t) using tc1 Stackloc Some using 7(3) 2(11) unfolding TypeSafe_def typeCompat_def by force+
              next
                case (KCDptr x2)
                then show ?thesis apply(cases t) using tc1 Stackloc Some using 7(3) 2(11) unfolding TypeSafe_def typeCompat_def by force+
              next
                case (KMemptr x3)
                then show ?thesis apply(cases t) using tc1 Stackloc Some using 7(3) 2(11) unfolding TypeSafe_def typeCompat_def by force+
              next
                case (KStoptr x4)
                then have accO:"accessStore x1 (Stack st) = Some( KStoptr x4)"
                  using Some 2 by auto
                then obtain struct where structDef: "t = type.Storage struct"
                  using 7(3) unfolding TypeSafe_def typeCompat_def using tc1 Some KStoptr Stackloc
                  by (cases t) fastforce+
                have tOld: "Type (Accounts st (Address e)) = Some (atype.Contract (environment.Contract e))"
                  using "7.prems"(3) unfolding fullyInitialised_def by auto
                obtain tprnt lprnt where tprntDef: "((type.Storage tprnt, Storeloc lprnt) |\<in>| fmran (Denvalue e) \<and> CompStoType tprnt struct lprnt x4)"
                  using 7(5) using accO tc1 unfolding fullyInitialised_def
                  using Stackloc structDef by blast
                then have "SCon tprnt lprnt (Storage st'' (Address e))"
                  using ctoDef IH1 fi4 ct1 scNew
                  by (metis (no_types, lifting) "7.prems"(2,3) tOld
                      accFinal fi_denvalue_storeloc_to_contract_var atype_same)

                then have "SCon struct x4 (Storage st'' (Address e))"
                  using tprntDef SCon_imps_sublocs by blast
                then show ?thesis using Stackloc Some KStoptr structDef storageFinal by simp
              qed
            qed
          next
            case (Storeloc x2)
            then obtain struct where structDef: "t = type.Storage struct"
              using 7(3) tc1 unfolding TypeSafe_def typeCompat_def by (cases t,fastforce+)

            then have "SCon struct x2 (Storage st'' (Address e))"
              using ctoDef IH1 fi4 ct1 scNew fmlookup_ran_iff fullyInitialised_def "7.prems"(3)
            proof -
              have "Type (Accounts st (Address e)) = Some (atype.Contract (environment.Contract e))"
                using "7.prems"(3) unfolding fullyInitialised_def by auto
              then have "Type (Accounts st'' (Address e)) = Some (atype.Contract (environment.Contract e))"
                using atype_same[OF "7.prems"(2)] accFinal by simp
              moreover have "ctO $$ x2 = Some (Var struct)"
                using fi_denvalue_storeloc_to_contract_var[OF "7.prems"(3) ctoDef] tc1 Storeloc structDef by simp
              ultimately show ?thesis using scNew ctoDef by blast
            qed

            then show ?thesis using Storeloc structDef
              by (simp add: storageFinal)
          qed
        qed
      next
        show "denvalueTypeCorrectness e (Stack st') (Memory st')" using 2(11) 7(3) unfolding TypeSafe_def by simp
      next
        show "subPrefixStructuralConsistency (Memory st')" using 2(11) 7(3) unfolding TypeSafe_def by simp
      next
        show "SomeValSomeTyp (Memory st')" using 2(11) 7(3) unfolding TypeSafe_def by simp
      qed
    next
      have fiOld:"
        \<exists>c ct dud.
          Type (Accounts st (Address e)) = Some (atype.Contract c) \<and>
          Contract e = c \<and>
          ep $$ c = Some (ct, dud) \<and>
          (\<forall>id v. (ct $$ id = Some (Var v)) = (Denvalue e $$ id = Some (type.Storage v, Storeloc id))) \<and>
          (\<forall>id v loc. Denvalue e $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc) \<and>
          (\<forall>t l p.
              (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l (Stack st) = Some (KStoptr p) \<longrightarrow>
              (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e) \<and> CompStoType t' t l' p))"
        using 7(5) unfolding fullyInitialised_def by blast
      then obtain c_fi ct_fi dud_fi where fiC:"
          Type (Accounts st (Address e)) = Some (atype.Contract c_fi) \<and>
          Contract e = c_fi \<and>
          ep $$ c_fi = Some (ct_fi, dud_fi) \<and>
          (\<forall>id v. (ct_fi $$ id = Some (Var v)) = (Denvalue e $$ id = Some (type.Storage v, Storeloc id))) \<and>
          (\<forall>id v loc. Denvalue e $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc)"
        and fiPtr:"\<forall>t l p.
              (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l (Stack st) = Some (KStoptr p) \<longrightarrow>
              (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e) \<and> CompStoType t' t l' p)"
        by blast
      have typeNew:"Type (Accounts st' (Address e)) = Some (atype.Contract c_fi)"
        using fiC atype_same "7.prems"(2,3) statement_with_gas.atype_same statement_with_gas_axioms by blast
      have ptrNew:"\<forall>t l p.
           (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l (Stack st') = Some (KStoptr p) \<longrightarrow>
           (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e) \<and> CompStoType t' t l' p)"
        using 7(5) 2 unfolding fullyInitialised_def by auto
      show "fullyInitialised e (Accounts st') (Stack st')"
        unfolding fullyInitialised_def using fiC fiPtr ptrNew typeNew by blast
    next
      show "\<And>locs t. accessTypeStore locs (Memory st) = Some t \<Longrightarrow> accessTypeStore locs (Memory st') = Some t"
        using 7(3) 2(11) by simp
    next
      show "\<And>locs v.
       accessStore locs (Memory st) = Some (MPointer v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MPointer v')"
        using 2(11) by simp
    next
      show "\<And>locs v. accessStore locs (Memory st) = Some (MValue v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MValue v')"
        using 2(11) by simp
    next
      show "\<And>i loc.
       i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<Longrightarrow>
       accessStore loc (Memory st) = None \<Longrightarrow> accessStore loc (Memory st') = None"
        using 2(11) by simp
    next
      show "Toploc (Memory st) \<le> Toploc (Memory st')"
        using 2(11) by simp
    qed
  qed
next
  case (8 ad ex e cd st)
  show ?case
  proof(cases rule:transfer[OF 8(3)])
    case (1 v t g adv c g' v' acc ct cn f st'')
    then obtain cc :: environment where ccDef: "Contract cc = c"
      by (meson Environment.select_convs(2))
    then have a1:"assert Gas (\<lambda>st. costs (TRANSFER ad ex) e cd st < state.Gas st) st = Normal ((), st)" using 1 by simp
    have a10:"modify (\<lambda>st. st\<lparr>Gas := state.Gas st - costs (TRANSFER ad ex) e cd st\<rparr>) st = Normal ((), st\<lparr>Gas := state.Gas st - costs (TRANSFER ad ex) e cd st\<rparr>)"
      by simp
    have a20:"toState (local.expr ad e cd) (st\<lparr>Gas := state.Gas st - costs (TRANSFER ad ex) e cd st\<rparr>) = Normal ((KValue adv, Value TAddr), st\<lparr>Gas := g\<rparr>)"
      using 1 by simp
    then have a30:"(case (KValue adv, Value TAddr) of (KValue adv, Value TAddr) \<Rightarrow> return adv | (KValue adv, Value _)
        \<Rightarrow> throw Err | (KValue adv, _) \<Rightarrow> throw Err | (_, b) \<Rightarrow> throw Err)
     (st\<lparr>Gas := g\<rparr>) = Normal (adv, st\<lparr>Gas := g\<rparr>)" using 1 by simp
    have a40:" toState (local.expr ex e cd) (st\<lparr>Gas := g\<rparr>) = Normal ((KValue v, Value t), st\<lparr>Gas := g'\<rparr>)" using 1 by auto
    have a50:"(case (KValue v, Value t) of (KValue v, Value t) \<Rightarrow> return (v, t) | (KValue v, _) \<Rightarrow> throw Err | (_, b)
        \<Rightarrow> throw Err) (st\<lparr>Gas := g'\<rparr>) = Normal ((v, t), (st\<lparr>Gas := g'\<rparr>))"
      using 1 by simp
    then have a60:"option Err (\<lambda>_. convert t (TUInt b256) v) (st\<lparr>Gas := g'\<rparr>) = Normal (v', st\<lparr>Gas := g'\<rparr>)" using 1 by simp
    have a70:"applyf Accounts (st\<lparr>Gas := g'\<rparr>) = Normal (Accounts (st\<lparr>Gas := g\<rparr>), (st\<lparr>Gas := g'\<rparr>))" using 1 by simp
    have a80:"Type (Accounts (st\<lparr>Gas := g\<rparr>) adv) = Some (atype.Contract c)" using 1(5) by blast
    have a90:"option Err (\<lambda>st. transfer (Address e) adv v' (Accounts st)) (st\<lparr>Gas := g'\<rparr>) = Normal (acc, (st\<lparr>Gas := g'\<rparr>))"
      using 1 by simp
    have a95:"option Err (\<lambda>_. ep $$ c) (st\<lparr>Gas := g'\<rparr>) = Normal ((ct, cn, f), (st\<lparr>Gas := g'\<rparr>))" using 1 by auto
    have a100:"modify (\<lambda>st. st\<lparr>Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>) (st\<lparr>Gas := g'\<rparr>)
                  = Normal ((), st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>)" by simp
    obtain loaded where loadedDef:"loaded = ffold_init ct (emptyEnv adv c (Address e) v') (fmdom ct)" by blast

    have tsLoaded':"\<forall>x y. TypeSafe loaded acc emptyStore emptyTypedStore (Storage st) emptyTypedStore \<and>
       (Denvalue loaded $$ x = Some y \<longrightarrow> snd y = Storeloc x) \<and> (Denvalue loaded $$ x = Some y \<longrightarrow>
           (\<exists>t1. ct $$ x = Some (Var t1) \<and> fst y = type.Storage t1))"
    proof -
      have "safeContract (Accounts st) (Storage st)" using 8(2) unfolding TypeSafe_def AddressTypes_def using 1 by simp
      moreover have "safeContract acc (Storage st)"
        using "1"(7) calculation safeContract_def transfer_type_same by force
      moreover have svv':"svalueTypes v'" unfolding svalueTypes_def
        using 1(4,3) 8(2) 8(4)
        using exprTypeconInduct(3)[of ex e cd "(st\<lparr>Gas := g\<rparr>)" g "KValue v" "Value t" g']
          typeSafeConvert[of t v "(TUInt b256)"] convertSame by auto
      moreover have "balanceTypes acc" unfolding balanceTypes_def
      proof -
        have old:"balanceTypes (Accounts (st\<lparr>Gas := g'\<rparr>))" using 8(2) unfolding TypeSafe_def by simp
        have accExp:"(case subBalance (Address e) v' (Accounts (st)) of None \<Rightarrow> None | Some x \<Rightarrow> addBalance adv v' x) = Some acc"
          using 1(7) unfolding transfer_def by blast
        have v'TC: "typeCon (TUInt b256) v'"
          using svv' unfolding svalueTypes_def by blast

        show "\<forall>adv'. typeCon (TUInt b256) (Bal (acc adv')) "
        proof(cases "adv = (Address e)")
          case same:True
          show ?thesis using transfer_sameRead
            by (metis "1"(7) "8"(2) balanceTypes_def same typeSafeAccounts transfer_eq v'TC)
        next
          case notSame:False
          show ?thesis
          proof
            fix adv'
            show "typeCon (TUInt b256) (Bal (acc adv')) "
            proof(cases "adv' = (Address e)")
              case True
              then have tco:"typeCon (TUInt b256) (Bal ((Accounts (st\<lparr>Gas := g'\<rparr>)) adv'))"
                using True old accExp balanceTypes_def by blast
              have "Bal (acc (Address e)) = ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts (st\<lparr>Gas :=
                  g'\<rparr>) (Address e))) - (ReadL\<^sub>i\<^sub>n\<^sub>t v'))"
                using transfer_subRead[OF 1(7) _ v'TC ] True notSame tco by auto
              then show ?thesis using True
                using "1"(7,3) Read_ShowL_id \<open>typeCon (TUInt b256) (Bal (Accounts (st\<lparr>Gas := g'\<rparr>) adv'))\<close> checkUInt_def transfer_val1 transfer_val2
              proof -
                have "\<forall>a. typeCon (TUInt b256) (Bal (Accounts st a))"
                  using old unfolding balanceTypes_def by simp
                then show ?thesis using transfer_Bal_typeCon[unfolded transfer_def, OF accExp] by blast
              qed
            next
              case False
              then show ?thesis
              proof(cases "adv' = adv")
                case True
                then have "typeCon (TUInt b256) (Bal (Accounts (st\<lparr>Gas := g'\<rparr>) adv))"
                  using True old accExp balanceTypes_def by simp
                then have "Bal (acc adv) = (ShowL\<^sub>i\<^sub>n\<^sub>t ((ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts (st\<lparr>Gas := g'\<rparr>) adv))) + (ReadL\<^sub>i\<^sub>n\<^sub>t v')))"
                  using transfer_addRead[OF 1(7)_ v'TC ] 1(3) notSame by auto
                then show ?thesis using True
                  using "1"(7,3) Read_ShowL_id \<open>typeCon (TUInt b256) (Bal (Accounts (st\<lparr>Gas := g'\<rparr>) adv))\<close> checkUInt_def transfer_val1 transfer_val2 notSame by auto
              next
                case f2:False
                then show ?thesis using False transfer_eq[OF 1(7)] old
                  using balanceTypes_def by force
              qed
            qed
          qed
        qed
      qed
      moreover have "lessThanTopLocs emptyStore" using emptyTopLocs by simp
      moreover have "ep $$ Contract cc = Some (ct, cn, f)" using ccDef 1(6) by simp
      moreover have "addressFormat adv" using 8(2) unfolding TypeSafe_def AddressTypes_def using 1 by (simp split:option.splits atype.splits)
      moreover have "addressFormat (Sender e)" using 8(2) unfolding TypeSafe_def AddressTypes_def using 1 by simp
      moreover have "AddressTypes acc" using 1(7) transfer_type_same 8(2) unfolding TypeSafe_def unfolding AddressTypes_def by simp
      moreover have "addressFormat (Address e)" using "8.prems"(1) unfolding TypeSafe_def by simp
      moreover have "SomeValSomeTyp emptyTypedStore" unfolding SomeValSomeTyp_def accessTypeStore_def accessStore_def emptyTypedStore_def by auto
      moreover have sp:"subPrefixStructuralConsistency emptyTypedStore" unfolding subPrefixStructuralConsistency_def accessTypeStore_def emptyTypedStore_def by simp
      moreover have "Type (acc adv) = Some (atype.Contract (Contract cc))"
        using a80 ccDef transfer_type_same[OF 1(7)] by simp
      ultimately show ?thesis
        using loadedDef ccDef unfolding ffold_init_def
        using ffoldInitTypeSafe[of acc "Storage st" v' emptyTypedStore cc ct "(cn,f)" adv "(Address e)" " (fmdom ct)"]
        using typedEmptyTopLocs
        by blast
    qed
    then have tsLoaded:"TypeSafe loaded (Accounts (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>))
     (Stack (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>)) (Memory (st\<lparr>Gas := g',
         Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>))
     (Storage (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>)) emptyTypedStore" by auto

    have contractL:"Contract loaded = c" using loadedDef by simp
    have addressL:"Address loaded = adv" using loadedDef by simp
    have fi1:"(\<exists>c. Type (Accounts (st\<lparr>Gas := g'\<rparr>) (Address loaded)) = Some (atype.Contract c) \<and> Contract loaded = c)" using contractL addressL 1 a10 a40 by simp
    have ctd:"\<exists>dud. ep $$ Contract loaded = Some (ct, dud)" using a50 contractL 1 a10 by blast
    then have fi2:"\<forall>id v. (Denvalue loaded $$ id = Some (type.Storage v, Storeloc id)) = (ct $$ id = Some (Var v))"
      using loadedDef unfolding ffold_init_def using ffoldInit_var_storage_mapping_eq[of ct adv c "(Address e)" v' loaded] by auto
    then have fi3:"(\<exists>c. Type ((acc) (Address loaded)) = Some (atype.Contract c) \<and> Contract loaded = c)"
      using fi1 contractL 1(7) transfer_type_same by simp
    have fi4:"(\<forall>id v. \<exists>dud. ep $$ Contract loaded = Some (ct, dud)
                          \<and> ct $$ id = Some (Var v) = (Denvalue loaded $$ id = Some (type.Storage v, Storeloc id)))"
      using fi1 ctd fi2
      by (metis (mono_tags, opaque_lifting))
    have fiLoaded:"fullyInitialised loaded (Accounts (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory :=
        emptyTypedStore\<rparr>)) (Stack (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>))"
    proof -
      obtain c_fi where cfi0:"Type (acc (Address loaded)) = Some (atype.Contract c_fi) \<and> Contract loaded = c_fi"
        using fi3 by blast
      have cfi:"Type (Accounts (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>) (Address loaded))
            = Some (atype.Contract c_fi) \<and> Contract loaded = c_fi"
        using cfi0 by simp
      obtain dud_fi where epfi:"ep $$ Contract loaded = Some (ct, dud_fi)"
        using ctd by blast
      have mapfi:"\<forall>id v. (ct $$ id = Some (Var v)) = (Denvalue loaded $$ id = Some (type.Storage v, Storeloc id))"
        using fi2 by blast
      have locfi:"\<forall>id v loc. Denvalue loaded $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc"
      proof (intro allI impI)
        fix id v loc
        assume h:"Denvalue loaded $$ id = Some (type.Storage v, Storeloc loc)"
        have hloc:"Denvalue loaded $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> snd (type.Storage v, Storeloc loc) = Storeloc id"
          using tsLoaded' by blast
        then show "id = loc" using h by simp
      qed
      have ptrfi:"\<forall>t l p.
          (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue loaded) \<and>
          accessStore l (Stack (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>)) = Some (KStoptr p) \<longrightarrow>
          (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue loaded) \<and> CompStoType t' t l' p)"
        by (simp add: accessStore_def emptyStore_def)
      show ?thesis
        unfolding fullyInitialised_def using cfi epfi mapfi locfi ptrfi by blast
    qed
    have stmtC:"stmt f loaded emptyTypedStore (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>) = Normal ((), st'')"
      using 1(8) loadedDef unfolding ffold_init_def by simp
    have IH1:"StateInvariant loaded (st\<lparr>Gas := g', Accounts := acc, Stack := emptyStore, Memory := emptyTypedStore\<rparr>) st'' emptyTypedStore"
      using 8(1)[OF a1 a10 a20 a30 a40 a50 _ a60 a70 a80 _ a95 _ _ loadedDef _ _ a90 a100 tsLoaded stmtC fiLoaded ] by simp

    have acc:"(\<forall>adv. case Type (Accounts st adv) of None \<Rightarrow> True | Some EOA \<Rightarrow> True | Some (atype.Contract c) \<Rightarrow> addressFormat adv \<and> c |\<in>| fmdom ep)"
      using 8(2) unfolding TypeSafe_def AddressTypes_def by blast
    obtain cOld where "Type (Accounts st (Address e)) = Some (atype.Contract cOld) \<and> Contract e = cOld"
      using 8(4) unfolding fullyInitialised_def by simp
    then obtain ctO dudO where ctoDef: "ep $$ Contract e = Some (ctO, dudO)" using acc
      using "8.prems"(3) typesafe_base.fullyInitialised_def typesafe_base_axioms by blast
    have storageFinal:"Storage st' = Storage st''" using 1 by auto

    have ct1:"\<exists>dud. ep $$ Contract loaded = Some (ct, dud)" using a50 contractL 1 a10 by blast
    have SafeC:"safeContract (Accounts st'') (Storage st'')" using IH1 unfolding StateInvariant_def TypeSafe_def by blast

    then have scNew:"\<forall>e ct dud i tp. Type (Accounts st'' (Address e)) = Some (atype.Contract (environment.Contract e))
                      \<and> ep $$ Contract (e::environment) = Some (ct, dud) \<and> ct $$ i = Some (Var tp) \<longrightarrow> SCon tp i (Storage st'' (Address e))"
      using SafeC unfolding safeContract_def by simp
    have accFinal:"Accounts st' = Accounts st''" using 1 by simp

    show ?thesis unfolding StateInvariant_def
    proof intros
      show "TypeSafe e (Accounts st') (Stack st') (Memory st') (Storage st') cd" unfolding TypeSafe_def
      proof intros
        show "AddressTypes (Accounts st')" using IH1 unfolding StateInvariant_def TypeSafe_def using 1 by simp
      next
        show "safeContract (Accounts st') (Storage st')" using IH1 1 unfolding StateInvariant_def TypeSafe_def by auto
      next
        show "unique_locations (Denvalue e)" using "8.prems"(1) typeSafeUnique by blast
      next
        have "compPointers (Stack st'') (Denvalue loaded)"
          using IH1 unfolding StateInvariant_def TypeSafe_def by blast
        show "compPointers (Stack st') (Denvalue e)" unfolding compPointers_def
        proof intros
          fix tp1 tp2 l1 l2 l1' l2' stl1 stl2
          assume a0:"(type.Storage tp1, l1) |\<in>| fmran (Denvalue e) \<and>
       (type.Storage tp2, l2) |\<in>| fmran (Denvalue e) \<and>
       (l1 = Stackloc l1' \<and> accessStore l1' (Stack st') = Some (KStoptr stl1) \<or> l1 = Storeloc stl1) \<and>
       (l2 = Stackloc l2' \<and> accessStore l2' (Stack st') = Some (KStoptr stl2) \<or> l2 = Storeloc stl2)"
          then have a5:"accessStore l1' (Stack st') = accessStore l1' (Stack st)" using 1 by simp
          have a10:"accessStore l2' (Stack st') = accessStore l2' (Stack st)" using 1 by auto
          show "if TypedStoSubpref stl2 stl1 tp1 then CompStoType tp1 tp2 stl1 stl2
                else if TypedStoSubpref stl1 stl2 tp2 then CompStoType tp2 tp1 stl2 stl1 else True"
            using 8(2) unfolding TypeSafe_def compPointers_def using a0 a5 a10 by simp
        qed
      next
        show "balanceTypes (Accounts st')" using 1 IH1 unfolding StateInvariant_def TypeSafe_def by auto
      next
        have "envAddressesWellFormed e" using "8.prems"(1) unfolding TypeSafe_def by simp
        then show "addressFormat (Address e)" and "addressFormat (Sender e)" by simp+
      next
        show "svalueTypes (Svalue e)" using "8.prems"(1) unfolding TypeSafe_def by simp
      next
        show "lessThanTopLocs (Stack st')" using 1 "8.prems"(1) unfolding TypeSafe_def by simp
      next
        show "lessThanTopLocs cd" using "8.prems"(1) unfolding TypeSafe_def by simp
      next
        show "lessThanTopLocs (Memory st')" using 1 "8.prems"(1) unfolding TypeSafe_def by simp
      next
        show "typeCompat (Denvalue e) (Stack st') (Memory st') (Storage st' (Address e)) cd"
          unfolding typeCompat_def
        proof intros
          fix t l
          assume tc1:"(t, l) |\<in>| fmran (Denvalue e)"
          show "denvalueCon (Stack st') (Memory st') (Storage st' (Address e)) cd t l"
          proof(cases l)
            case (Stackloc x1)
            then show ?thesis
            proof(cases "accessStore x1 (Stack st')")
              case None
              then show ?thesis using tc1 Stackloc using 8(2) 1 unfolding TypeSafe_def typeCompat_def by force
            next
              case (Some a)
              then show ?thesis
              proof(cases a)
                case (KValue x1)
                then show ?thesis apply(cases t) using tc1 Stackloc Some using 8(2) 1(9) unfolding TypeSafe_def typeCompat_def by force+
              next
                case (KCDptr x2)
                then show ?thesis apply(cases t) using tc1 Stackloc Some using 8(2) 1(9) unfolding TypeSafe_def typeCompat_def by force+
              next
                case (KMemptr x3)
                then show ?thesis apply(cases t) using tc1 Stackloc Some using 8(2) 1(9) unfolding TypeSafe_def typeCompat_def by force+
              next
                case (KStoptr x4)
                then have accO:"accessStore x1 (Stack st) = Some( KStoptr x4)"
                  using Some 1 KStoptr by auto
                then obtain struct where structDef: "t = type.Storage struct"
                  using 8(2) unfolding TypeSafe_def typeCompat_def using tc1 Some KStoptr Stackloc
                  by (cases t) fastforce+
                have tOld: "Type (Accounts st (Address e)) = Some (atype.Contract (environment.Contract e))"
                  using "8.prems"(3) unfolding fullyInitialised_def by auto
                obtain tprnt lprnt where tprntDef: "((type.Storage tprnt, Storeloc lprnt) |\<in>| fmran (Denvalue e) \<and> CompStoType tprnt struct lprnt x4)"
                  using 8(4) using accO tc1 unfolding fullyInitialised_def
                  using Stackloc structDef by blast

                then have "SCon tprnt lprnt (Storage st'' (Address e))"
                  using ctoDef IH1 fi4 ct1 scNew
                    "8.prems"(2,3) tOld
                      fi_denvalue_storeloc_to_contract_var atype_same accFinal
                  by (metis (no_types, lifting))

                then have "SCon struct x4 (Storage st'' (Address e))"
                  using tprntDef SCon_imps_sublocs by blast
                then show ?thesis using Stackloc Some KStoptr structDef storageFinal by simp
              qed
            qed
          next
            case (Storeloc x2)
            then obtain struct where structDef: "t = type.Storage struct"
              using 8(2) tc1 unfolding TypeSafe_def typeCompat_def by (cases t,fastforce+)

            then have "SCon struct x2 (Storage st'' (Address e))"
              using ctoDef IH1 fi4 ct1 scNew fmlookup_ran_iff fullyInitialised_def "8.prems"(3)
            proof -
              have "Type (Accounts st (Address e)) = Some (atype.Contract (environment.Contract e))"
                using "8.prems"(3) unfolding fullyInitialised_def by auto
              then have "Type (Accounts st'' (Address e)) = Some (atype.Contract (environment.Contract e))"
                using atype_same[OF "8.prems"(2)] accFinal by simp
              moreover have "ctO $$ x2 = Some (Var struct)"
                using fi_denvalue_storeloc_to_contract_var[OF "8.prems"(3) ctoDef] tc1 Storeloc structDef by simp
              ultimately show ?thesis using scNew ctoDef by blast
            qed

            then show ?thesis using Storeloc structDef
              by (simp add: storageFinal)
          qed
        qed
      next
        show "denvalueTypeCorrectness e (Stack st') (Memory st')" using 1 8(2) unfolding TypeSafe_def by simp
      next
        show "subPrefixStructuralConsistency (Memory st')" using 1 8(2) unfolding TypeSafe_def by simp
      next
        show "SomeValSomeTyp (Memory st')" using 1 8(2) unfolding TypeSafe_def by simp
      qed
    next
      have fiOld:"
        \<exists>c ct dud.
          Type (Accounts st (Address e)) = Some (atype.Contract c) \<and>
          Contract e = c \<and>
          ep $$ c = Some (ct, dud) \<and>
          (\<forall>id v. (ct $$ id = Some (Var v)) = (Denvalue e $$ id = Some (type.Storage v, Storeloc id))) \<and>
          (\<forall>id v loc. Denvalue e $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc) \<and>
          (\<forall>t l p.
              (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l (Stack st) = Some (KStoptr p) \<longrightarrow>
              (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e) \<and> CompStoType t' t l' p))"
        using 8(4) unfolding fullyInitialised_def by blast
      then obtain c_fi ct_fi dud_fi where fiC:"
          Type (Accounts st (Address e)) = Some (atype.Contract c_fi) \<and>
          Contract e = c_fi \<and>
          ep $$ c_fi = Some (ct_fi, dud_fi) \<and>
          (\<forall>id v. (ct_fi $$ id = Some (Var v)) = (Denvalue e $$ id = Some (type.Storage v, Storeloc id))) \<and>
          (\<forall>id v loc. Denvalue e $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc)"
        and fiPtr:"\<forall>t l p.
              (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l (Stack st) = Some (KStoptr p) \<longrightarrow>
              (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e) \<and> CompStoType t' t l' p)"
        by blast
      have typeNew:"Type (Accounts st' (Address e)) = Some (atype.Contract c_fi)"
        using fiC atype_same "8.prems"(2,3) statement_with_gas.atype_same statement_with_gas_axioms by blast
      have ptrNew:"\<forall>t l p.
           (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l (Stack st') = Some (KStoptr p) \<longrightarrow>
           (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e) \<and> CompStoType t' t l' p)"
        using 8(4) 1 unfolding fullyInitialised_def by auto
      show "fullyInitialised e (Accounts st') (Stack st')"
        unfolding fullyInitialised_def using fiC fiPtr ptrNew typeNew by blast
    next
      show "\<And>locs t. accessTypeStore locs (Memory st) = Some t \<Longrightarrow> accessTypeStore locs (Memory st') = Some t"
        using 8(3) 1(9) by simp
    next
      show "\<And>locs v.
       accessStore locs (Memory st) = Some (MPointer v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MPointer v')"
        using 1(9) by simp
    next
      show "\<And>locs v. accessStore locs (Memory st) = Some (MValue v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MValue v')"
        using 1(9) by simp
    next
      show "\<And>i loc.
       i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<Longrightarrow>
       accessStore loc (Memory st) = None \<Longrightarrow> accessStore loc (Memory st') = None"
        using 1(9) by simp
    next
      show "Toploc (Memory st) \<le> Toploc (Memory st')" using 1(9) by simp

    qed
  next
    case (2 v t g adv g' v' acc)
    then have a1:"assert Gas (\<lambda>st. costs (TRANSFER ad ex) e cd st < state.Gas st) st = Normal ((), st)" by simp
    have a10:"modify (\<lambda>st. st\<lparr>Gas := state.Gas st - costs (TRANSFER ad ex) e cd st\<rparr>) st = Normal ((), st\<lparr>Gas := state.Gas st - costs (TRANSFER ad ex) e cd st\<rparr>)"
      by simp
    have a20:"toState (local.expr ad e cd) (st\<lparr>Gas := state.Gas st - costs (TRANSFER ad ex) e cd st\<rparr>) = Normal ((KValue adv, Value TAddr), st\<lparr>Gas := g\<rparr>)"
      using 2 by simp
    then have a30:"(case (KValue adv, Value TAddr) of (KValue adv, Value TAddr) \<Rightarrow> return adv | (KValue adv, Value _)
        \<Rightarrow> throw Err | (KValue adv, _) \<Rightarrow> throw Err | (_, b) \<Rightarrow> throw Err)
     (st\<lparr>Gas := g\<rparr>) = Normal (adv, st\<lparr>Gas := g\<rparr>)" using 2 by simp
    have a40:" toState (local.expr ex e cd) (st\<lparr>Gas := g\<rparr>) = Normal ((KValue v, Value t), st\<lparr>Gas := g'\<rparr>)" using 2 by auto
    have a50:"(case (KValue v, Value t) of (KValue v, Value t) \<Rightarrow> return (v, t) | (KValue v, _) \<Rightarrow> throw Err | (_, b)
        \<Rightarrow> throw Err) (st\<lparr>Gas := g'\<rparr>) = Normal ((v, t), (st\<lparr>Gas := g'\<rparr>))"
      using 2 by simp
    then have a60:"option Err (\<lambda>_. convert t (TUInt b256) v) (st\<lparr>Gas := g'\<rparr>) = Normal (v', st\<lparr>Gas := g'\<rparr>)" using 2 by simp
    have a70:"applyf Accounts (st\<lparr>Gas := g'\<rparr>) = Normal (Accounts (st\<lparr>Gas := g\<rparr>), (st\<lparr>Gas := g'\<rparr>))" using 2 by simp
    have a90:"option Err (\<lambda>st. transfer (Address e) adv v' (Accounts st)) (st\<lparr>Gas := g'\<rparr>) = Normal (acc, (st\<lparr>Gas := g'\<rparr>))"
      using 2 by simp

    have svv':"svalueTypes v'" unfolding svalueTypes_def
      using 2(4,3) 8(2) 8(4)
      using exprTypeconInduct(3)[of ex e cd "(st\<lparr>Gas := g\<rparr>)" g "KValue v" "Value t" g']
        typeSafeConvert[of t v "(TUInt b256)"] convertSame by auto

    have btACC:"balanceTypes acc" unfolding balanceTypes_def
    proof -
      have old:"balanceTypes (Accounts (st\<lparr>Gas := g'\<rparr>))" using 8(2) unfolding TypeSafe_def by simp
      have accExp:"(case subBalance (Address e) v' (Accounts (st)) of None \<Rightarrow> None | Some x \<Rightarrow> addBalance adv v' x) = Some acc"
        using 2(6) unfolding transfer_def by blast
      have v'TC: "typeCon (TUInt b256) v'"
        using svv' unfolding svalueTypes_def by blast

      show "\<forall>adv'. typeCon (TUInt b256) (Bal (acc adv')) "
      proof(cases "adv = (Address e)")
        case same:True
        show ?thesis using transfer_sameRead
          by (metis "2"(6) "8"(2) balanceTypes_def same typeSafeAccounts transfer_eq v'TC)
      next
        case notSame:False
        show ?thesis
        proof
          fix adv'
          show "typeCon (TUInt b256) (Bal (acc adv')) "
          proof(cases "adv' = (Address e)")
            case True
            then have tco:"typeCon (TUInt b256) (Bal ((Accounts (st\<lparr>Gas := g'\<rparr>)) adv'))"
              using True old accExp balanceTypes_def by blast
            have "Bal (acc (Address e)) = ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts (st\<lparr>Gas := g'\<rparr>) (Address e))) - (ReadL\<^sub>i\<^sub>n\<^sub>t v'))"
              using transfer_subRead[OF 2(6) _ v'TC ] True notSame tco by auto
            then show ?thesis using True
              using "2"(6,3) Read_ShowL_id \<open>typeCon (TUInt b256) (Bal (Accounts (st\<lparr>Gas := g'\<rparr>) adv'))\<close> checkUInt_def transfer_val1 transfer_val2
            proof -
              have "\<forall>a. typeCon (TUInt b256) (Bal (Accounts st a))"
                using old unfolding balanceTypes_def by simp
              then show ?thesis using transfer_Bal_typeCon[unfolded transfer_def, OF accExp] by blast
            qed
          next
            case False
            then show ?thesis
            proof(cases "adv' = adv")
              case True
              then have "typeCon (TUInt b256) (Bal (Accounts (st\<lparr>Gas := g'\<rparr>) adv))"
                using True old accExp balanceTypes_def by simp
              then have "Bal (acc adv) = (ShowL\<^sub>i\<^sub>n\<^sub>t ((ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts (st\<lparr>Gas := g'\<rparr>) adv))) + (ReadL\<^sub>i\<^sub>n\<^sub>t v')))"
                using transfer_addRead[OF 2(6)_ v'TC ] 2(3) notSame by auto
              then show ?thesis using True
                using "2"(6,3) Read_ShowL_id \<open>typeCon (TUInt b256) (Bal (Accounts (st\<lparr>Gas := g'\<rparr>) adv))\<close> checkUInt_def transfer_val1 transfer_val2 notSame by auto
            next
              case f2:False
              then show ?thesis using False transfer_eq[OF 2(6)] old
                using balanceTypes_def by force
            qed
          qed
        qed
      qed
    qed

    have accfinal:"Accounts st'= acc" using 2 by simp

    have sameStores:"Storage st' = Storage st \<and> Memory st = Memory st' \<and> Stack st = Stack st'" using 2 by simp
    show ?thesis unfolding StateInvariant_def
    proof intros
      show "TypeSafe e (Accounts st') (Stack st') (Memory st') (Storage st') cd" unfolding TypeSafe_def
      proof intros
        show "AddressTypes (Accounts st')" unfolding AddressTypes_def
        proof intros
          fix adv
          show "case Type (Accounts st' adv) of None \<Rightarrow> True | Some EOA \<Rightarrow> True | Some (atype.Contract c) \<Rightarrow> addressFormat adv \<and> c |\<in>| fmdom ep"
          proof (cases "Type (Accounts st' adv)")
            case None
            then show ?thesis by simp
          next
            case (Some a)
            then show ?thesis
            proof(cases a)
              case EOA
              then show ?thesis using Some by simp
            next
              case (Contract x2)
              then show ?thesis using Some 8(2) unfolding TypeSafe_def using accfinal 2(6) transfer_type_same
                by (metis transfer_type_same accfinal Some "2"(6) AddressTypes_def)
            qed
          qed
        qed
      next
        show "safeContract (Accounts st') (Storage st')" using 8(2) 2 unfolding TypeSafe_def using sameStores
        proof -
          have "safeContract (Accounts st) (Storage st')" using 8(2) sameStores unfolding TypeSafe_def by simp
          moreover have "\<forall>a. Type (Accounts st' a) = Type (Accounts st a)"
            using transfer_type_same[OF "2"(6)] accfinal by simp
          ultimately show ?thesis by (rule safeContract_Type_cong)
        qed
      next
        show "unique_locations (Denvalue e)" using 8(2) unfolding TypeSafe_def using sameStores by simp
      next
        show "compPointers (Stack st') (Denvalue e)" using 8(2) unfolding TypeSafe_def using sameStores by simp
      next
        show "balanceTypes (Accounts st')" using btACC accfinal by simp
      next
        have "envAddressesWellFormed e" using "8.prems"(1) unfolding TypeSafe_def by simp
        then show "addressFormat (Address e)" and "addressFormat (Sender e)" by simp+
      next
        show "svalueTypes (Svalue e)" using "8.prems"(1) unfolding TypeSafe_def by simp
      next
        show "lessThanTopLocs (Stack st')" using 8(2) unfolding TypeSafe_def using sameStores by simp
      next
        show "lessThanTopLocs cd" using "8.prems"(1) unfolding TypeSafe_def by simp
      next
        show "lessThanTopLocs (Memory st')" using 8(2) unfolding TypeSafe_def using sameStores by simp
      next
        show "typeCompat (Denvalue e) (Stack st') (Memory st') (Storage st' (Address e)) cd"
          using 8(2) unfolding TypeSafe_def using sameStores by simp
      next
        show "denvalueTypeCorrectness e (Stack st') (Memory st')" using 8(2) unfolding TypeSafe_def using sameStores by simp
      next
        show "subPrefixStructuralConsistency (Memory st')" using 8(2) unfolding TypeSafe_def using sameStores by simp
      next
        show "SomeValSomeTyp (Memory st')" using 8(2) unfolding TypeSafe_def using sameStores by simp
      qed
    next
      have fiOld:"
              \<exists>c ct dud.
                Type (Accounts st (Address e)) = Some (atype.Contract c) \<and>
                Contract e = c \<and>
                ep $$ c = Some (ct, dud) \<and>
                (\<forall>id v. (ct $$ id = Some (Var v)) = (Denvalue e $$ id = Some (type.Storage v, Storeloc id))) \<and>
                (\<forall>id v loc. Denvalue e $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc) \<and>
                (\<forall>t l p.
                    (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l (Stack st) = Some (KStoptr p) \<longrightarrow>
                    (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e) \<and> CompStoType t' t l' p))"
        using 8(4) unfolding fullyInitialised_def by blast
      then obtain c_fi ct_fi dud_fi where fiC:"
          Type (Accounts st (Address e)) = Some (atype.Contract c_fi) \<and>
          Contract e = c_fi \<and>
          ep $$ c_fi = Some (ct_fi, dud_fi) \<and>
          (\<forall>id v. (ct_fi $$ id = Some (Var v)) = (Denvalue e $$ id = Some (type.Storage v, Storeloc id))) \<and>
          (\<forall>id v loc. Denvalue e $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc)"
        and fiPtr:"\<forall>t l p.
              (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l (Stack st) = Some (KStoptr p) \<longrightarrow>
              (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e) \<and> CompStoType t' t l' p)"
        by blast
      have typeNew:"Type (Accounts st' (Address e)) = Some (atype.Contract c_fi)"
        using fiC atype_same "8.prems"(2,3) statement_with_gas.atype_same statement_with_gas_axioms by blast
      have ptrNew:"\<forall>t l p.
           (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l (Stack st') = Some (KStoptr p) \<longrightarrow>
           (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e) \<and> CompStoType t' t l' p)"
        using 8(4) 2 unfolding fullyInitialised_def by auto
      show "fullyInitialised e (Accounts st') (Stack st')"
        unfolding fullyInitialised_def using fiC fiPtr ptrNew typeNew by blast
    next
      show "\<And>locs t. accessTypeStore locs (Memory st) = Some t \<Longrightarrow> accessTypeStore locs (Memory st') = Some t"
        using 8(3) 2(7) by simp
    next
      show "\<And>locs v.
       accessStore locs (Memory st) = Some (MPointer v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MPointer v')"
        using 2(7) by simp
    next
      show "\<And>locs v. accessStore locs (Memory st) = Some (MValue v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MValue v')"
        using 2(7) by simp
    next
      show "\<And>i loc.
       i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<Longrightarrow>
       accessStore loc (Memory st) = None \<Longrightarrow> accessStore loc (Memory st') = None"
        using 2(7) by simp
    next
      show "Toploc (Memory st) \<le> Toploc (Memory st')" using 2(7) by simp
    qed
  qed
next
  case (9 id0 tp s e\<^sub>v cd st)
  show ?case
  proof(cases rule:blockNone[OF 9(3)])
    case (1 cd' mem' sck' e')
    have a10:"assert Gas (\<lambda>st. costs (BLOCK (id0, tp, None) s) e\<^sub>v cd st < state.Gas st) st = Normal ((), st)" using 1 by simp
    obtain sgas where sgasDef:"sgas = state.Gas st - costs (BLOCK (id0, tp, None) s) e\<^sub>v cd st" by simp
    then have a20:"modify (\<lambda>st. st\<lparr>Gas := state.Gas st - costs (BLOCK (id0, tp, None) s) e\<^sub>v cd st\<rparr>) st = Normal ((), (st\<lparr>Gas := sgas\<rparr> ))" by simp
    have a30:"option Err (\<lambda>st. decl id0 tp None False cd (Memory st) (Storage st (Address e\<^sub>v)) (cd, Memory st, Stack st, e\<^sub>v)) (st\<lparr>Gas := sgas\<rparr> )
            = Normal ((cd', mem', sck', e'), (st\<lparr>Gas := sgas\<rparr> )) " using 1 by simp
    have a40:"modify (\<lambda>st. st\<lparr>Stack := sck', Memory := mem'\<rparr>) (st\<lparr>Gas := sgas\<rparr>) = Normal ((), st\<lparr>Gas := sgas, Stack := sck', Memory := mem'\<rparr>)"
      by simp

    have tsDecl:"TypeSafe e' (Accounts (st\<lparr>Gas := state.Gas st - costs (BLOCK (id0, tp, None) s) e\<^sub>v cd st\<rparr>)) sck' mem'
     (Storage (st\<lparr>Gas := state.Gas st - costs (BLOCK (id0, tp, None) s) e\<^sub>v cd st\<rparr>)) cd' \<and>
    (\<forall>x l. (\<nexists>y y'. x = type.Memory y \<or> x = Value y') \<and> (x, l) |\<in>| fmran (Denvalue e') \<longrightarrow>
           (x, l) |\<in>| fmran (Denvalue e\<^sub>v)) \<and>
    (\<forall>sckl ptr.
        accessStore sckl sck' = Some ptr \<and> (\<nexists>y y'. ptr = KMemptr y \<or> ptr = KValue y') \<longrightarrow>
        accessStore sckl (Stack (st\<lparr>Gas := state.Gas st - costs (BLOCK (id0, tp, None) s) e\<^sub>v cd st\<rparr>)) =
        Some ptr) \<and>
    cd = cd'\<and>
    Toploc (Memory (st\<lparr>Gas := state.Gas st - costs (BLOCK (id0, tp, None) s) e\<^sub>v cd st\<rparr>)) \<le> Toploc mem' \<and>
    (\<forall>locs v.
        accessStore locs (Memory (st\<lparr>Gas := state.Gas st - costs (BLOCK (id0, tp, None) s) e\<^sub>v cd st\<rparr>)) = Some v \<longrightarrow>
        accessStore locs mem' = Some v) \<and>
    (\<forall>locs t.
        accessTypeStore locs (Memory (st\<lparr>Gas := state.Gas st - costs (BLOCK (id0, tp, None) s) e\<^sub>v cd st\<rparr>)) = Some t \<longrightarrow>
        accessTypeStore locs mem' = Some t) \<and>
    (\<forall>locs.
        (\<exists>tloc<Toploc (Memory (st\<lparr>Gas := state.Gas st - costs (BLOCK (id0, tp, None) s) e\<^sub>v cd st\<rparr>)).
            LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t tloc) \<and>
            accessStore locs (Memory (st\<lparr>Gas := state.Gas st - costs (BLOCK (id0, tp, None) s) e\<^sub>v cd st\<rparr>)) = None) \<longrightarrow>
        accessStore locs mem' = None)"
      using typeSafeDeclNone[OF _ 1(2)] 9(2) by simp

    then have a50:"TypeSafe e' (Accounts (st\<lparr>Gas := sgas, Stack := sck', Memory := mem'\<rparr>)) (Stack (st\<lparr>Gas := sgas, Stack := sck', Memory := mem'\<rparr>))
   (Memory (st\<lparr>Gas := sgas, Stack := sck', Memory := mem'\<rparr>)) (Storage (st\<lparr>Gas := sgas, Stack := sck', Memory := mem'\<rparr>)) cd'" by simp
    have denLink:"\<forall>ii x. Denvalue e\<^sub>v $$ ii = Some x \<longrightarrow> Denvalue e' $$ ii = Some x" using decl_env_monotonic[OF 1(2)] by auto

    have fiDec:" fullyInitialised e' (Accounts (st\<lparr>Gas := sgas, Stack := sck', Memory := mem'\<rparr>)) (Stack (st\<lparr>Gas := sgas, Stack := sck', Memory := mem'\<rparr>))"
    proof -
      have sameStuff:"Address e' = Address e\<^sub>v \<and> Contract e' = Contract e\<^sub>v"
        using 1(2) decl_env by simp
      have fiOld:"
        \<exists>c ct dud.
          Type (Accounts st (Address e\<^sub>v)) = Some (atype.Contract c) \<and>
          Contract e\<^sub>v = c \<and>
          ep $$ c = Some (ct, dud) \<and>
          (\<forall>id v. (ct $$ id = Some (Var v)) = (Denvalue e\<^sub>v $$ id = Some (type.Storage v, Storeloc id))) \<and>
          (\<forall>id v loc. Denvalue e\<^sub>v $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc) \<and>
          (\<forall>t l p.
              (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e\<^sub>v) \<and> accessStore l (Stack st) = Some (KStoptr p) \<longrightarrow>
              (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e\<^sub>v) \<and> CompStoType t' t l' p))"
        using 9(4) unfolding fullyInitialised_def by blast
      then obtain c_fi ct_fi dud_fi where fiC:"
          Type (Accounts st (Address e\<^sub>v)) = Some (atype.Contract c_fi) \<and>
          Contract e\<^sub>v = c_fi \<and>
          ep $$ c_fi = Some (ct_fi, dud_fi) \<and>
          (\<forall>id v. (ct_fi $$ id = Some (Var v)) = (Denvalue e\<^sub>v $$ id = Some (type.Storage v, Storeloc id))) \<and>
          (\<forall>id v loc. Denvalue e\<^sub>v $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc)"
        and fiPtr:"\<forall>t l p.
              (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e\<^sub>v) \<and> accessStore l (Stack st) = Some (KStoptr p) \<longrightarrow>
              (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e\<^sub>v) \<and> CompStoType t' t l' p)"
        by blast

      have cfi:"Type (Accounts (st\<lparr>Gas := sgas, Stack := sck', Memory := mem'\<rparr>) (Address e')) = Some (atype.Contract c_fi) \<and>
          Contract e' = c_fi \<and> ep $$ c_fi = Some (ct_fi, dud_fi)"
        using fiC sameStuff by simp

      have mapfi:"\<forall>id v. (ct_fi $$ id = Some (Var v)) = (Denvalue e' $$ id = Some (type.Storage v, Storeloc id))"
      proof (intro allI)
        fix id v
        show "(ct_fi $$ id = Some (Var v)) = (Denvalue e' $$ id = Some (type.Storage v, Storeloc id))"
        proof
          assume hct:"ct_fi $$ id = Some (Var v)"
          then have "Denvalue e\<^sub>v $$ id = Some (type.Storage v, Storeloc id)"
            using fiC by blast
          then show "Denvalue e' $$ id = Some (type.Storage v, Storeloc id)"
            using decl_env_monotonic[OF 1(2)] by blast
        next
          assume hnew:"Denvalue e' $$ id = Some (type.Storage v, Storeloc id)"
          show "ct_fi $$ id = Some (Var v)"
          proof (cases "id = id0")
            case True
            have "\<forall>t l. Denvalue e' $$ id0 = Some (t, Storeloc l) \<longrightarrow> Denvalue e\<^sub>v $$ id0 = Some (t, Storeloc l)"
              using decl_env_storlocs_unchanged[OF 1(2)] by simp
            then have "Denvalue e\<^sub>v $$ id0 = Some (type.Storage v, Storeloc id0)"
              using hnew True by blast
            then show ?thesis using fiC True by blast
          next
            case False
            then have "Denvalue e\<^sub>v $$ id = Some (type.Storage v, Storeloc id)"
              using decl_env_not_i[OF 1(2)] hnew by blast
            then show ?thesis using fiC by blast
          qed
        qed
      qed

      have locfi:"\<forall>id v loc. Denvalue e' $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc"
      proof (intro allI impI)
        fix id v loc
        assume hnew:"Denvalue e' $$ id = Some (type.Storage v, Storeloc loc)"
        show "id = loc"
        proof (cases "id = id0")
          case True
          have "\<forall>t l. Denvalue e' $$ id0 = Some (t, Storeloc l) \<longrightarrow> Denvalue e\<^sub>v $$ id0 = Some (t, Storeloc l)"
            using decl_env_storlocs_unchanged[OF 1(2)] by simp
          then have "Denvalue e\<^sub>v $$ id0 = Some (type.Storage v, Storeloc loc)"
            using hnew True by blast
          then have "id0 = loc" using fiC by blast
          then show ?thesis using True by simp
        next
          case False
          then have "Denvalue e\<^sub>v $$ id = Some (type.Storage v, Storeloc loc)"
            using decl_env_not_i[OF 1(2)] hnew by blast
          then show ?thesis using fiC by blast
        qed
      qed

      have ptrfi:"\<forall>t l p.
          (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e') \<and>
          accessStore l (Stack (st\<lparr>Gas := sgas, Stack := sck', Memory := mem'\<rparr>)) = Some (KStoptr p) \<longrightarrow>
          (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e') \<and> CompStoType t' t l' p)"
      proof (intro allI impI)
        fix t l p
        assume in1:"(type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e') \<and>
            accessStore l (Stack (st\<lparr>Gas := sgas, Stack := sck', Memory := mem'\<rparr>)) = Some (KStoptr p)"
        have inOld:"(type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e\<^sub>v)" using tsDecl in1 by simp
        have accOld:"accessStore l (Stack st) = Some (KStoptr p)" using tsDecl in1 by simp
        from fiPtr inOld accOld obtain t' l' where oldRan:
            "(type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e\<^sub>v)"
            and comp:"CompStoType t' t l' p"
          by blast
        from oldRan obtain idp where idpDef:"Denvalue e\<^sub>v $$ idp = Some (type.Storage t', Storeloc l')"
          using fmlookup_ran_iff by fast
        have "Denvalue e' $$ idp = Some (type.Storage t', Storeloc l')"
          using decl_env_monotonic[OF 1(2)] idpDef by blast
        then have newRan:"(type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e')"
          by (meson fmranI)
        show "\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e') \<and> CompStoType t' t l' p"
          using newRan comp by blast
      qed

      show ?thesis
        unfolding fullyInitialised_def using cfi mapfi locfi ptrfi by blast
    qed

    have IH1:"StateInvariant e' (st\<lparr>Gas := sgas, Stack := sck', Memory := mem'\<rparr>) st' cd'"
      using 9(1)[OF a10 a20 a30, of cd' "(mem', sck', e')" mem' "(sck', e')" sck' e', OF _ _ _ a40 a50 _ fiDec, of st'] 1(3) sgasDef by simp
    then have fiFinal:" fullyInitialised e' (Accounts st') (Stack st')"
      unfolding StateInvariant_def by blast
    have sameAdd:"Address e' = Address e\<^sub>v" using 1(2) decl_env by simp
    show ?thesis unfolding StateInvariant_def
    proof intros
      show "TypeSafe e\<^sub>v (Accounts st') (Stack st') (Memory st') (Storage st') cd" unfolding TypeSafe_def
      proof intros
        show "AddressTypes (Accounts st')" using IH1 unfolding StateInvariant_def TypeSafe_def by blast
      next
        show "safeContract (Accounts st') (Storage st')" using IH1 unfolding StateInvariant_def TypeSafe_def by blast
      next
        show "unique_locations (Denvalue e\<^sub>v)" using 9(2) unfolding TypeSafe_def by simp
      next
        have cpNew:"(\<forall>tp1 tp2 l1 l2 l1' l2' stl1 stl2.
       (type.Storage tp1, l1) |\<in>| fmran (Denvalue e') \<and>
       (type.Storage tp2, l2) |\<in>| fmran (Denvalue e') \<and>
       (l1 = Stackloc l1' \<and> accessStore l1' (Stack st') = Some (KStoptr stl1) \<or> l1 = Storeloc stl1) \<and>
       (l2 = Stackloc l2' \<and> accessStore l2' (Stack st') = Some (KStoptr stl2) \<or> l2 = Storeloc stl2) \<longrightarrow>
       (if TypedStoSubpref stl2 stl1 tp1 then CompStoType tp1 tp2 stl1 stl2 else if TypedStoSubpref stl1 stl2 tp2 then CompStoType tp2 tp1 stl2 stl1 else True))"
          using IH1 unfolding StateInvariant_def TypeSafe_def compPointers_def by auto
        show "compPointers (Stack st') (Denvalue e\<^sub>v)" unfolding compPointers_def
        proof intros
          fix tp1 tp2 l1 l2 l1' l2' stl1 stl2
          assume a0:"(type.Storage tp1, l1) |\<in>| fmran (Denvalue e\<^sub>v) \<and>
       (type.Storage tp2, l2) |\<in>| fmran (Denvalue e\<^sub>v) \<and>
       (l1 = Stackloc l1' \<and> accessStore l1' (Stack st') = Some (KStoptr stl1) \<or> l1 = Storeloc stl1) \<and>
       (l2 = Stackloc l2' \<and> accessStore l2' (Stack st') = Some (KStoptr stl2) \<or> l2 = Storeloc stl2)"
          then obtain i1 i2 where iDefs:" (Denvalue e\<^sub>v) $$ i1 = Some (type.Storage tp1, l1)
                                  \<and> (Denvalue e\<^sub>v) $$ i2 = Some (type.Storage tp2, l2)" by blast
          then have "(type.Storage tp1, l1) |\<in>| fmran (Denvalue e') \<and> (type.Storage tp2, l2) |\<in>| fmran (Denvalue e')" using a0
            by (metis denLink fmlookup_ran_iff)
          then show "if TypedStoSubpref stl2 stl1 tp1 then CompStoType tp1 tp2 stl1 stl2
                else if TypedStoSubpref stl1 stl2 tp2 then CompStoType tp2 tp1 stl2 stl1 else True"
            using cpNew using a0 by blast
        qed
      next
        show "balanceTypes (Accounts st')" using IH1 unfolding StateInvariant_def TypeSafe_def by blast
      next
        have "envAddressesWellFormed e\<^sub>v" using 9(2) unfolding TypeSafe_def by simp
        then show "addressFormat (Address e\<^sub>v)" and "addressFormat (Sender e\<^sub>v)" by simp+
      next
        show "svalueTypes (Svalue e\<^sub>v)" using 9(2) unfolding TypeSafe_def by simp
      next
        show "lessThanTopLocs (Stack st')" using IH1 unfolding StateInvariant_def TypeSafe_def by blast
      next
        show "lessThanTopLocs cd" using 9(2) unfolding TypeSafe_def by simp
      next
        show "lessThanTopLocs (Memory st')" using IH1 unfolding StateInvariant_def TypeSafe_def by blast
      next
        have oldTC:"typeCompat (Denvalue e') (Stack st') (Memory st') (Storage st' (Address e')) cd'"
          using IH1 unfolding StateInvariant_def TypeSafe_def by blast
        show "typeCompat (Denvalue e\<^sub>v) (Stack st') (Memory st') (Storage st' (Address e\<^sub>v)) cd"
          unfolding typeCompat_def
        proof intros
          fix t l
          assume inDen:"(t, l) |\<in>| fmran (Denvalue e\<^sub>v)"
          then have inDenN:"(t, l) |\<in>| fmran (Denvalue e')"
            using denLink by (meson fmlookup_ran_iff)

          show "denvalueCon (Stack st') (Memory st') (Storage st' (Address e\<^sub>v)) cd t l"
          proof(cases l)
            case (Stackloc x1)
            then have oldTC':"(
             case accessStore x1 (Stack st') of None \<Rightarrow> False
              | Some (KValue val) \<Rightarrow> (case t of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
              | Some (KCDptr stloc) \<Rightarrow> (case t of Calldata struct \<Rightarrow> MCon struct cd' stloc | _ \<Rightarrow> False)
              | Some (KMemptr stloc) \<Rightarrow> (case t of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
              | Some (KStoptr stloc) \<Rightarrow> (case t of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address e')) | _ \<Rightarrow> False))"
              using oldTC unfolding typeCompat_def using inDenN by fastforce
            then show ?thesis
            proof(cases "accessStore x1 (Stack st')")
              case None
              then show ?thesis using oldTC unfolding typeCompat_def using inDenN sameAdd Stackloc by fastforce
            next
              case (Some a)
              then show ?thesis
              proof(cases a)
                case (KValue x1')
                then show ?thesis using oldTC unfolding typeCompat_def using inDenN sameAdd Some Stackloc by force
              next
                case (KCDptr x2)
                then obtain struct where structDef:"t = Calldata struct \<and> MCon struct cd' x2"
                  using oldTC' unfolding typeCompat_def using inDenN sameAdd Some Stackloc by (cases t; auto)
                then show ?thesis using tsDecl KCDptr Some Stackloc by simp
              next
                case (KMemptr x3)
                then show ?thesis using oldTC unfolding typeCompat_def using inDenN sameAdd Some Stackloc by fastforce
              next
                case (KStoptr x4)
                then have "case t of type.Storage struct \<Rightarrow> SCon struct x4 (Storage st' (Address e')) | _ \<Rightarrow> False"
                  using oldTC' using inDenN sameAdd Some Stackloc by (auto split:option.splits type.splits stackvalue.splits denvalue.splits)
                then obtain struct where "t = type.Storage struct \<and> SCon struct x4 (Storage st' (Address e'))" by (cases t; auto)
                then show ?thesis using Some Stackloc KStoptr
                  by (simp add: sameAdd)
              qed
            qed
          next
            case (Storeloc x2)
            then show ?thesis using oldTC unfolding typeCompat_def using inDenN sameAdd
              by (metis (no_types, lifting) denvalue.simps(6) type.exhaust type.simps(17,18,19,20))
          qed
        qed
      next
        show "denvalueTypeCorrectness e\<^sub>v (Stack st') (Memory st')"
          unfolding denvalueTypeCorrectness_def
        proof intros
          fix t l ptr_loc sub_loc
          assume in1:"(type.Memory t, Stackloc l) |\<in>| fmran (Denvalue e\<^sub>v) \<and> accessStore l (Stack st') = Some (KMemptr ptr_loc)"
          then have in2:"(type.Memory t, Stackloc l) |\<in>| fmran (Denvalue e')" using denLink
            by (meson fmlookup_ran_iff)
          then show " case t of MTArray len arr \<Rightarrow> \<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr
       | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st') = Some (MTValue val)"
            using IH1 unfolding StateInvariant_def TypeSafe_def denvalueTypeCorrectness_def
            using in1 in2 by blast
        qed
      next
        show "subPrefixStructuralConsistency (Memory st')" using IH1 unfolding StateInvariant_def TypeSafe_def by simp
      next
        show "SomeValSomeTyp (Memory st')" using IH1 unfolding StateInvariant_def TypeSafe_def by simp
      qed
    next
      have fiOld:"
        \<exists>c ct dud.
          Type (Accounts st (Address e\<^sub>v)) = Some (atype.Contract c) \<and>
          Contract e\<^sub>v = c \<and>
          ep $$ c = Some (ct, dud) \<and>
          (\<forall>id v. (ct $$ id = Some (Var v)) = (Denvalue e\<^sub>v $$ id = Some (type.Storage v, Storeloc id))) \<and>
          (\<forall>id v loc. Denvalue e\<^sub>v $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc) \<and>
          (\<forall>t l p.
              (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e\<^sub>v) \<and> accessStore l (Stack st) = Some (KStoptr p) \<longrightarrow>
              (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e\<^sub>v) \<and> CompStoType t' t l' p))"
        using 9(4) unfolding fullyInitialised_def by blast
      then obtain c_fi ct_fi dud_fi where fiC:"
          Type (Accounts st (Address e\<^sub>v)) = Some (atype.Contract c_fi) \<and>
          Contract e\<^sub>v = c_fi \<and>
          ep $$ c_fi = Some (ct_fi, dud_fi) \<and>
          (\<forall>id v. (ct_fi $$ id = Some (Var v)) = (Denvalue e\<^sub>v $$ id = Some (type.Storage v, Storeloc id))) \<and>
          (\<forall>id v loc. Denvalue e\<^sub>v $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc)"
        and fiPtr:"\<forall>t l p.
              (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e\<^sub>v) \<and> accessStore l (Stack st) = Some (KStoptr p) \<longrightarrow>
              (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e\<^sub>v) \<and> CompStoType t' t l' p)"
        by blast
      have typeNew:"Type (Accounts st' (Address e\<^sub>v)) = Some (atype.Contract c_fi)"
        using fiC atype_same "9.prems"(2,3) statement_with_gas.atype_same statement_with_gas_axioms by blast
      have ptrNew:"\<forall>t l p.
           (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e\<^sub>v) \<and> accessStore l (Stack st') = Some (KStoptr p) \<longrightarrow>
           (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e\<^sub>v) \<and> CompStoType t' t l' p)"
      proof (intro allI impI)
        fix t l p
        assume in1:"(type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e\<^sub>v) \<and> accessStore l (Stack st') = Some (KStoptr p)"
        have inNew:"(type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e')"
          using denLink in1 by (meson fmlookup_ran_iff)
        from fiFinal inNew in1 obtain t' l' where newPtr:
            "(type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e')"
            and comp:"CompStoType t' t l' p"
          unfolding fullyInitialised_def by blast
        from newPtr obtain iid where iidDef:"Denvalue e' $$ iid = Some (type.Storage t', Storeloc l')"
          using fmlookup_ran_iff by fast
        have oldLookup:"Denvalue e\<^sub>v $$ iid = Some (type.Storage t', Storeloc l')"
        proof (cases "iid = id0")
          case True
          have "\<forall>t l. Denvalue e' $$ id0 = Some (t, Storeloc l) \<longrightarrow> Denvalue e\<^sub>v $$ id0 = Some (t, Storeloc l)"
            using decl_env_storlocs_unchanged[OF 1(2)] by simp
          then show ?thesis using iidDef True by blast
        next
          case False
          then show ?thesis using decl_env_not_i[OF 1(2) iidDef] by blast
        qed
        have oldRan:"(type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e\<^sub>v)"
          using oldLookup by (meson fmranI)
        show "\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e\<^sub>v) \<and> CompStoType t' t l' p"
          using oldRan comp by blast
      qed
      show "fullyInitialised e\<^sub>v (Accounts st') (Stack st')"
        unfolding fullyInitialised_def using fiC fiPtr ptrNew typeNew by blast
    next
      fix locs t
      assume in1:"accessTypeStore locs (Memory st) = Some t"
      then have same:"accessTypeStore locs (Memory st) = accessTypeStore locs mem'"
        using tsDecl in1 by simp
      then have "accessTypeStore locs (mem') = Some t"
        using in1 by simp
      then show "accessTypeStore locs (Memory st') = Some t"
        using in1 IH1 unfolding StateInvariant_def by simp
    next
      fix locs v
      assume in1:"accessStore locs (Memory st) = Some (MPointer v)"
      then have same:"accessStore locs (Memory st) = accessStore locs mem'"
        using tsDecl by simp
      then have "accessStore locs (mem') = Some (MPointer v)"
        using in1 by simp
      then show "\<exists>v'. accessStore locs (Memory st') = Some (MPointer v')"
        using in1 IH1 unfolding StateInvariant_def by simp
    next
      fix locs v
      assume in1:"accessStore locs (Memory st) = Some (MValue v)"
      then have same:"accessStore locs (Memory st) = accessStore locs mem'"
        using tsDecl unfolding ncpOMemInDMem_def by simp
      then have "accessStore locs (mem') = Some (MValue v)"
        using in1 by simp
      then show "\<exists>v'. accessStore locs (Memory st') = Some (MValue v')"
        using in1 IH1 unfolding StateInvariant_def by simp
    next
      fix i loc
      assume in1:"i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) "
        and in2:" accessStore loc (Memory st) = None"
      moreover have "Toploc (Memory st) \<le> Toploc mem'" using tsDecl unfolding ncpOMemInDMem_def by simp
      then have same:"accessStore loc (Memory st) = accessStore loc mem'"
        using tsDecl in1 by fastforce
      moreover have "i < Toploc (mem') \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)"
        using calculation in1
        using \<open>Toploc (Memory st) \<le> Toploc mem'\<close> order.strict_trans2 by blast
      ultimately have "accessStore loc mem' = None \<longrightarrow>
        accessStore loc (Memory st') = None" using IH1 unfolding StateInvariant_def by simp
      then show "accessStore loc (Memory st') = None" using in2 same by simp

    next
      show "Toploc (Memory st) \<le> Toploc (Memory st')"
        using 1 IH1 unfolding StateInvariant_def using tsDecl by simp
    qed
  qed
next
  case (10 id0 tp ex' s e\<^sub>v cd st)
  show ?case
  proof(cases rule:blockSome[OF 10(3)])
    case (1 v t g cd' mem' sck' e')
    have a10:"assert Gas (\<lambda>st. costs (BLOCK (id0, tp, Some ex') s) e\<^sub>v cd st < state.Gas st) st = Normal ((), st)" using 1 by simp
    obtain sgas where sgasDef:"sgas = state.Gas st - costs (BLOCK (id0, tp, Some ex') s) e\<^sub>v cd st" by simp
    then have a20:"modify (\<lambda>st. st\<lparr>Gas := state.Gas st - costs (BLOCK (id0, tp, Some ex') s) e\<^sub>v cd st\<rparr>) st = Normal ((), (st\<lparr>Gas := sgas\<rparr> ))" by simp
    have a25:"toState (local.expr ex' e\<^sub>v cd) (st\<lparr>Gas := sgas\<rparr> ) = Normal ((v, t), (st\<lparr>Gas := g\<rparr>))" using 1 sgasDef by auto
    have a30:"option Err (\<lambda>st. decl id0 tp (Some (v, t)) False cd (Memory st) (Storage st (Address e\<^sub>v)) (cd, Memory st, Stack st, e\<^sub>v)) (st\<lparr>Gas := g\<rparr> )
            = Normal ((cd', mem', sck', e'), (st\<lparr>Gas := g\<rparr> )) " using 1 by simp
    have a40:"modify (\<lambda>st. st\<lparr>Stack := sck', Memory := mem'\<rparr>) (st\<lparr>Gas := g\<rparr>) = Normal ((), st\<lparr>Gas := g, Stack := sck', Memory := mem'\<rparr>)"
      by simp

    have "\<exists>c ct dud.
       Type (Accounts st (Address e\<^sub>v)) = Some (atype.Contract c) \<and>
       environment.Contract e\<^sub>v = c \<and>
       ep $$ c = Some (ct, dud) \<and>
       (\<forall>id v. (ct $$ id = Some (Var v)) = (Denvalue e\<^sub>v $$ id = Some (type.Storage v, Storeloc id))) \<and>
       (\<forall>id v loc. Denvalue e\<^sub>v $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc) \<and>
       (\<forall>t l p.
           (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e\<^sub>v) \<and> accessStore l (Stack st) = Some (KStoptr p) \<longrightarrow>
           (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e\<^sub>v) \<and> CompStoType t' t l' p))"
      using sgasDef 10(4) unfolding fullyInitialised_def by simp
    moreover have "fullyInitialised e\<^sub>v (Accounts (st\<lparr>Gas := sgas\<rparr>)) (Stack (st\<lparr>Gas := sgas\<rparr>))"
      by (simp add: "10.prems"(3))
    moreover have tsSgas:"TypeSafe e\<^sub>v (Accounts (st\<lparr>Gas := sgas\<rparr>)) (Stack (st\<lparr>Gas := sgas\<rparr>)) (Memory
        (st\<lparr>Gas := sgas\<rparr>)) (Storage (st\<lparr>Gas := sgas\<rparr>)) cd" using 10(2) by simp
    ultimately have tcTV:"exprResultCon e\<^sub>v cd (st\<lparr>Gas := sgas\<rparr>) v t"
      using 1(2) exprTypeconInduct(3)[of ex' "e\<^sub>v" cd "st\<lparr>Gas := sgas\<rparr>" sgas v t g] sgasDef by blast
    then have tcTV':"valueCon e\<^sub>v cd (st\<lparr>Gas := g\<rparr>) v t"
      by (cases t, simp+)

    have tsDecl:"TypeSafe e' (Accounts (st\<lparr>Gas := g\<rparr>)) sck' mem' (Storage (st\<lparr>Gas := g\<rparr>)) cd' \<and>
    (\<not> False \<longrightarrow>
     (\<forall>locs tp. MCon tp (Memory (st\<lparr>Gas := g\<rparr>)) locs \<longrightarrow> MCon tp mem' locs) \<and>
     ncpDenvalueLimit e' e\<^sub>v sck' (Stack (st\<lparr>Gas := g\<rparr>)) (Memory (st\<lparr>Gas := g\<rparr>)) \<and>
     ncpOMemInDMem (Memory (st\<lparr>Gas := g\<rparr>)) mem' \<and> ncpElementsNoSubPref (Memory (st\<lparr>Gas := g\<rparr>)) mem'
\<and> ncpNewSelfPoint (Memory (st\<lparr>Gas := g\<rparr>)) mem') \<and> Toploc (Memory (st\<lparr>Gas := g\<rparr>)) \<le> Toploc mem'"
    proof -
      have tsgas:"TypeSafe e\<^sub>v (Accounts (st\<lparr>Gas := g\<rparr>)) (Stack (st\<lparr>Gas := g\<rparr>)) (Memory (st\<lparr>Gas := g\<rparr>)) (Storage (st\<lparr>Gas := g\<rparr>)) cd"
        using 10(2) by simp
      have "ncpDenvalueLimit e\<^sub>v e\<^sub>v (Stack (st\<lparr>Gas := g\<rparr>)) (Stack (st\<lparr>Gas := g\<rparr>)) (Memory (st\<lparr>Gas := g\<rparr>))"
        unfolding ncpDenvalueLimit_def by auto
      moreover have "ncpOMemInDMem (Memory (st\<lparr>Gas := g\<rparr>)) (Memory (st\<lparr>Gas := g\<rparr>))" unfolding ncpOMemInDMem_def by auto
      moreover have "ncpElementsNoSubPref (Memory (st\<lparr>Gas := g\<rparr>)) (Memory (st\<lparr>Gas := g\<rparr>))"
        using ncpElementsNoSubPref_def ncpElementsNoSubPref_sameMem tsgas by blast
      moreover have "ncpNewSelfPoint (Memory (st\<lparr>Gas := g\<rparr>)) (Memory (st\<lparr>Gas := g\<rparr>))"
        unfolding ncpNewSelfPoint_def by auto
      ultimately have acc0:"\<not> False \<longrightarrow>
    (\<forall>locs tp. MCon tp (Memory (st\<lparr>Gas := g\<rparr>)) locs \<longrightarrow> MCon tp (Memory (st\<lparr>Gas := g\<rparr>)) locs) \<and>
    Toploc (Memory (st\<lparr>Gas := g\<rparr>)) \<le> Toploc (Memory (st\<lparr>Gas := g\<rparr>)) \<and>
    ncpDenvalueLimit e\<^sub>v e\<^sub>v (Stack (st\<lparr>Gas := g\<rparr>)) (Stack (st\<lparr>Gas := g\<rparr>)) (Memory (st\<lparr>Gas := g\<rparr>)) \<and>
    ncpOMemInDMem (Memory (st\<lparr>Gas := g\<rparr>)) (Memory (st\<lparr>Gas := g\<rparr>)) \<and>
    ncpElementsNoSubPref (Memory (st\<lparr>Gas := g\<rparr>)) (Memory (st\<lparr>Gas := g\<rparr>)) \<and> ncpNewSelfPoint (Memory
        (st\<lparr>Gas := g\<rparr>)) (Memory (st\<lparr>Gas := g\<rparr>))" by blast
      have acc1:"\<forall>struct.
     t = type.Memory struct \<longrightarrow>
     (\<exists>stloc tp'' p.
         (type.Memory tp'', Stackloc stloc) |\<in>| fmran (Denvalue e\<^sub>v) \<and>
         accessStore stloc (Stack (st\<lparr>Gas := g\<rparr>)) = Some (KMemptr p) \<and>
         (tp'' = struct \<and> v = KMemptr p \<or>
          (\<exists>len arr. p \<noteq> extractValueType v \<and> tp'' = MTArray len arr \<and> CompMemType (Memory (st\<lparr>Gas := g\<rparr>)) len arr struct p (extractValueType v))))"
        using tcTV by (cases t, blast+; fastforce)
      have acc2:"\<forall>struct.
     t = Calldata struct \<longrightarrow>
     (\<exists>stloc tp'' p.
         (Calldata tp'', Stackloc stloc) |\<in>| fmran (Denvalue e\<^sub>v) \<and>
         accessStore stloc (Stack (st\<lparr>Gas := g\<rparr>)) = Some (KCDptr p) \<and>
         (tp'' = struct \<and> v = KCDptr p \<or> (\<exists>len arr. p \<noteq> extractValueType v \<and> tp'' = MTArray len arr \<and> CompMemType cd len arr struct p (extractValueType v))))"
        using tcTV by (cases t, blast+; fastforce)
      have acc3:"\<forall>struct.
       tp = type.Storage struct \<longrightarrow>
       (\<forall>locs tp. SCon tp locs (Storage (st\<lparr>Gas := g\<rparr>) (Address e\<^sub>v)) \<longrightarrow> SCon tp locs (Storage (st\<lparr>Gas := g\<rparr>) (Address e\<^sub>v))) \<and>
       (\<exists>stloc tp''.
           (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue e\<^sub>v) \<and>
           (tp'' = struct \<and> v = KStoptr stloc \<or> extractValueType v \<noteq> stloc \<and> CompStoType tp'' struct stloc (extractValueType v)))"
        using tcTV
      proof(cases t)
        case (Value x1)
        then have "\<forall>struct. tp \<noteq> type.Storage struct " using 1(3) decl_KValue_tp_match
          by blast
        then show ?thesis by simp
      next
        case (Calldata x2)
        then have "\<forall>struct. tp \<noteq> type.Storage struct " using 1(3) decl_Calldata_tp_match
          by blast
        then show ?thesis by simp
      next
        case (Memory x3)
        then have "\<forall>struct. tp \<noteq> type.Storage struct " using 1(3) decl_Memory_tp_match
          by blast
        then show ?thesis by simp
      next
        case (Storage x4)
        then have sc:"SCon x4 (extractValueType v) (Storage (st\<lparr>Gas := sgas\<rparr>) (Address e\<^sub>v)) \<and>
              (\<exists>xx. v = KStoptr xx) \<and>
              (\<exists>stloc tp''.
                  (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue e\<^sub>v) \<and>
                  tp'' = x4 \<and> v = KStoptr stloc \<or> extractValueType v \<noteq> stloc \<and> CompStoType tp'' x4 stloc (extractValueType v))"
          using tcTV by auto
        have tt:"(\<exists>x t' t''. x4 = STArray x t' \<and> cps2mTypeCompatible (STArray x t') (MTArray x t'')\<and> tp = type.Memory (MTArray x t'')) \<or> tp = type.Storage x4"
          using decl_Memory_tp_options[] 1(3) Storage by simp
        then show ?thesis
        proof(cases "tp = type.Storage x4")
          case True
          moreover have "(\<forall>locs tp. SCon tp locs (Storage (st\<lparr>Gas := g\<rparr>) (Address e\<^sub>v)) \<longrightarrow> SCon
              tp locs (Storage (st\<lparr>Gas := g\<rparr>) (Address e\<^sub>v)))" by auto
          moreover have "(Stack (st\<lparr>Gas := sgas\<rparr>)) = (Stack (st\<lparr>Gas := g\<rparr>))" by auto
          then have "(\<exists>stloc tp''.
           (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue e\<^sub>v) \<and>
           tp'' = x4 \<and> v = KStoptr stloc \<or> extractValueType v \<noteq> stloc \<and> CompStoType tp'' x4 stloc (extractValueType v))"
            using sc True Storage by presburger
          ultimately show ?thesis
            using Storage tcTV by auto
        next
          case False
          then have "(\<exists>x t' t''. x4 = STArray x t' \<and> cps2mTypeCompatible (STArray x t') (MTArray x t'')\<and> tp = type.Memory (MTArray x t''))"
            using tt by simp
          then show ?thesis by auto
        qed
      qed
      have " TypeSafe e' (Accounts (st\<lparr>Gas := g\<rparr>)) sck' mem' (Storage (st\<lparr>Gas := g\<rparr>)) cd' \<and>
    (\<not> False \<longrightarrow>
     (\<forall>locs tp. MCon tp (Memory (st\<lparr>Gas := g\<rparr>)) locs \<longrightarrow> MCon tp mem' locs) \<and>
     Toploc (Memory (st\<lparr>Gas := g\<rparr>)) \<le> Toploc mem' \<and>
     ncpDenvalueLimit e' e\<^sub>v sck' (Stack (st\<lparr>Gas := g\<rparr>)) (Memory (st\<lparr>Gas := g\<rparr>)) \<and>
     ncpOMemInDMem (Memory (st\<lparr>Gas := g\<rparr>)) mem' \<and>
     ncpElementsNoSubPref (Memory (st\<lparr>Gas := g\<rparr>)) mem' \<and>
     ncpNewSelfPoint (Memory (st\<lparr>Gas := g\<rparr>)) mem')
    "
        using typeSafeDecl[OF tsgas tcTV' tsgas 1(3) acc0 acc1 acc2 ] acc3 by fastforce
      then show ?thesis by simp
    qed


    then have a50:"TypeSafe e' (Accounts (st\<lparr>Gas := g, Stack := sck', Memory := mem'\<rparr>)) (Stack (st\<lparr>Gas := g, Stack := sck', Memory := mem'\<rparr>))
   (Memory (st\<lparr>Gas := g, Stack := sck', Memory := mem'\<rparr>)) (Storage (st\<lparr>Gas := g, Stack := sck', Memory := mem'\<rparr>)) cd'"
      using tsDecl by simp

    have fiDec:" fullyInitialised e' (Accounts (st\<lparr>Gas := g, Stack := sck', Memory := mem'\<rparr>)) (Stack (st\<lparr>Gas := g, Stack := sck', Memory := mem'\<rparr>))"
    proof -
      have sameStuff:"Address e' = Address e\<^sub>v \<and> Contract e' = Contract e\<^sub>v" using 1(3) decl_env by simp
      have fiOld:"
        \<exists>c ct dud.
          Type (Accounts st (Address e\<^sub>v)) = Some (atype.Contract c) \<and>
          Contract e\<^sub>v = c \<and>
          ep $$ c = Some (ct, dud) \<and>
          (\<forall>id v. (ct $$ id = Some (Var v)) = (Denvalue e\<^sub>v $$ id = Some (type.Storage v, Storeloc id))) \<and>
          (\<forall>id v loc. Denvalue e\<^sub>v $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc) \<and>
          (\<forall>t l p.
              (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e\<^sub>v) \<and> accessStore l (Stack st) = Some (KStoptr p) \<longrightarrow>
              (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e\<^sub>v) \<and> CompStoType t' t l' p))"
        using 10(4) unfolding fullyInitialised_def by blast
      then obtain c_fi ct_fi dud_fi where fiC:"
          Type (Accounts st (Address e\<^sub>v)) = Some (atype.Contract c_fi) \<and>
          Contract e\<^sub>v = c_fi \<and>
          ep $$ c_fi = Some (ct_fi, dud_fi) \<and>
          (\<forall>id v. (ct_fi $$ id = Some (Var v)) = (Denvalue e\<^sub>v $$ id = Some (type.Storage v, Storeloc id))) \<and>
          (\<forall>id v loc. Denvalue e\<^sub>v $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc)"
        and fiPtr:"\<forall>t l p.
              (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e\<^sub>v) \<and> accessStore l (Stack st) = Some (KStoptr p) \<longrightarrow>
              (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e\<^sub>v) \<and> CompStoType t' t l' p)"
        by blast

      have cfi:"Type (Accounts (st\<lparr>Gas := g, Stack := sck', Memory := mem'\<rparr>) (Address e')) = Some (atype.Contract c_fi) \<and>
          Contract e' = c_fi \<and> ep $$ c_fi = Some (ct_fi, dud_fi)"
        using fiC sameStuff by simp

      have mapfi:"\<forall>id v. (ct_fi $$ id = Some (Var v)) = (Denvalue e' $$ id = Some (type.Storage v, Storeloc id))"
      proof (intro allI)
        fix id v
        show "(ct_fi $$ id = Some (Var v)) = (Denvalue e' $$ id = Some (type.Storage v, Storeloc id))"
        proof
          assume hct:"ct_fi $$ id = Some (Var v)"
          then have "Denvalue e\<^sub>v $$ id = Some (type.Storage v, Storeloc id)"
            using fiC by blast
          then show "Denvalue e' $$ id = Some (type.Storage v, Storeloc id)"
            using decl_env_monotonic[OF 1(3)] by blast
        next
          assume hnew:"Denvalue e' $$ id = Some (type.Storage v, Storeloc id)"
          show "ct_fi $$ id = Some (Var v)"
          proof (cases "id = id0")
            case True
            have "\<forall>t l. Denvalue e' $$ id0 = Some (t, Storeloc l) \<longrightarrow> Denvalue e\<^sub>v $$ id0 = Some (t, Storeloc l)"
              using decl_env_storlocs_unchanged[OF 1(3)] by simp
            then have "Denvalue e\<^sub>v $$ id0 = Some (type.Storage v, Storeloc id0)"
              using hnew True by blast
            then show ?thesis using fiC True by blast
          next
            case False
            then have "Denvalue e\<^sub>v $$ id = Some (type.Storage v, Storeloc id)"
              using decl_env_not_i[OF 1(3)] hnew by blast
            then show ?thesis using fiC by blast
          qed
        qed
      qed

      have locfi:"\<forall>id v loc. Denvalue e' $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc"
      proof (intro allI impI)
        fix id v loc
        assume hnew:"Denvalue e' $$ id = Some (type.Storage v, Storeloc loc)"
        show "id = loc"
        proof (cases "id = id0")
          case True
          have "\<forall>t l. Denvalue e' $$ id0 = Some (t, Storeloc l) \<longrightarrow> Denvalue e\<^sub>v $$ id0 = Some (t, Storeloc l)"
            using decl_env_storlocs_unchanged[OF 1(3)] by simp
          then have "Denvalue e\<^sub>v $$ id0 = Some (type.Storage v, Storeloc loc)"
            using hnew True by blast
          then have "id0 = loc" using fiC by blast
          then show ?thesis using True by simp
        next
          case False
          then have "Denvalue e\<^sub>v $$ id = Some (type.Storage v, Storeloc loc)"
            using decl_env_not_i[OF 1(3)] hnew by blast
          then show ?thesis using fiC by blast
        qed
      qed

      have ptrfi:"\<forall>tt l p.
          (type.Storage tt, Stackloc l) |\<in>| fmran (Denvalue e') \<and>
          accessStore l (Stack (st\<lparr>Gas := g, Stack := sck', Memory := mem'\<rparr>)) = Some (KStoptr p) \<longrightarrow>
          (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e') \<and> CompStoType t' tt l' p)"
      proof (intro allI impI)
        fix tt l p
        assume in1:"(type.Storage tt, Stackloc l) |\<in>| fmran (Denvalue e')\<and>accessStore l (Stack (st\<lparr>Gas := g, Stack := sck', Memory := mem'\<rparr>)) = Some (KStoptr p)"
        then obtain idd where iddDef: "Denvalue e' $$ idd = Some (type.Storage tt, Stackloc l)" by auto
        show " \<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e') \<and> CompStoType t' tt l' p"
        proof(cases "idd = id0")
          case True
          then have ddd:"Denvalue e' $$ id0 = Some (type.Storage tt, Stackloc l)" using iddDef by simp
          then show ?thesis
          proof(cases "Denvalue e\<^sub>v $$ id0")
            case None
            have ldef:"l = (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Stack (st\<lparr>Gas := g\<rparr>))))" using decl_stack_top[OF 1(3) None] iddDef True by simp
            then obtain p2 where p2Def:"Some (v, t) = Some (KStoptr p2, type.Storage tt)"
              using ddd True decl_storage_tp[OF 1(3) None, of tt ] by blast
            then have dcc:"decl id0 tp (Some (KStoptr p2, type.Storage tt)) False cd (Memory (st\<lparr>Gas := g\<rparr>)) (Storage (st\<lparr>Gas := g\<rparr>) (Address e\<^sub>v))
       (cd, Memory (st\<lparr>Gas := g\<rparr>), Stack (st\<lparr>Gas := g\<rparr>), e\<^sub>v) =
      Some (cd', mem', sck', e')" using 1(3) True by simp
            then have "v = KStoptr p" using decl_stack_topLoc[OF dcc None] using in1 ldef p2Def by auto
            then have "(\<exists>stloc tp''.
            (type.Storage tp'', Storeloc stloc) |\<in>| fmran (Denvalue e\<^sub>v) \<and>
            (tp'' = tt \<and> v = KStoptr stloc \<or> p \<noteq> stloc \<and> CompStoType tp'' tt stloc p))"
              using tcTV 1(3) p2Def by auto
            then show ?thesis using decl_env_monotonic[OF 1(3)]
              by (metis CompStoType_sameLocNdTyp stackvalue.inject(4) \<open>v = KStoptr p\<close> fmlookup_ran_iff)
          next
            case (Some a)
            then have "e\<^sub>v = e' \<and> sck' = Stack st" using decl_some_same[OF 1(3)] by auto
            then have oldIn:"(type.Storage tt, Stackloc l) |\<in>| fmran (Denvalue e\<^sub>v) \<and> accessStore l (Stack st) = Some (KStoptr p)"
              using in1 by simp
            then show ?thesis using fiPtr
              using \<open>e\<^sub>v = e' \<and> sck' = Stack st\<close> by blast
          qed
        next
          case False
          then have oldD:"Denvalue e\<^sub>v $$ idd = Some (type.Storage tt, Stackloc l)"
            using iddDef in1 1 decl_env_not_i[OF 1(3)] by blast
          then show ?thesis
          proof(cases "l = ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc (Stack st))")
            case True
            then show ?thesis
              by (metis "10.prems"(1) True oldD snd_conv stackLocs_imp_NotDen TypeSafe_def)
          next
            case False
            then have "accessStore l (Stack (st\<lparr>Gas := g, Stack := sck', Memory := mem'\<rparr>)) = accessStore l (Stack (st))"
              using decl_stack_change[OF 1(3)] by simp
            then have oldAcc:"accessStore l (Stack st) = Some (KStoptr p)" using in1 by simp
            from fiPtr oldD oldAcc obtain t' l' where t'Def: "(type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e\<^sub>v) \<and> CompStoType t' tt l' p"
              by (meson fmranI)
            then have "(type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e')"
              using decl_env_monotonic[OF 1(3)] by (meson fmlookup_ran_iff)
            then show ?thesis using t'Def by auto
          qed
        qed
      qed
      show ?thesis
        unfolding fullyInitialised_def using cfi mapfi locfi ptrfi by blast
    qed
    have sameCD:"cd = cd'" using decl_env_false_same_cd[OF 1(3)] by simp
    have IH1:" StateInvariant e' (st\<lparr>Gas := g, Stack := sck', Memory := mem'\<rparr>) st' cd'"
      using 10(1)[OF a10 a20 a25 _ a30, of cd' "(mem', sck', e')" mem' "(sck', e')" sck' e', OF _ _ _ _ a40 a50 _ fiDec, of st'] 1(4) sgasDef by simp

    have denLink:"\<forall>ii x. Denvalue e\<^sub>v $$ ii = Some x \<longrightarrow> Denvalue e' $$ ii = Some x" using decl_env_monotonic[OF 1(3)] by auto
    have sameAdd:"Address e' = Address e\<^sub>v"using 1(3) decl_env by simp
    show ?thesis unfolding StateInvariant_def
    proof intros
      show "TypeSafe e\<^sub>v (Accounts st') (Stack st') (Memory st') (Storage st') cd" unfolding TypeSafe_def
      proof intros
        show "AddressTypes (Accounts st')" using IH1 unfolding StateInvariant_def TypeSafe_def by blast
      next
        show "safeContract (Accounts st') (Storage st')" using IH1 unfolding StateInvariant_def TypeSafe_def by blast
      next
        show "unique_locations (Denvalue e\<^sub>v)" using 10(2) unfolding TypeSafe_def by simp
      next
        have cpNew:"(\<forall>tp1 tp2 l1 l2 l1' l2' stl1 stl2.
       (type.Storage tp1, l1) |\<in>| fmran (Denvalue e') \<and>
       (type.Storage tp2, l2) |\<in>| fmran (Denvalue e') \<and>
       (l1 = Stackloc l1' \<and> accessStore l1' (Stack st') = Some (KStoptr stl1) \<or> l1 = Storeloc stl1) \<and>
       (l2 = Stackloc l2' \<and> accessStore l2' (Stack st') = Some (KStoptr stl2) \<or> l2 = Storeloc stl2) \<longrightarrow>
       (if TypedStoSubpref stl2 stl1 tp1 then CompStoType tp1 tp2 stl1 stl2 else if TypedStoSubpref stl1 stl2 tp2 then CompStoType tp2 tp1 stl2 stl1 else True))"
          using IH1 unfolding StateInvariant_def TypeSafe_def compPointers_def by auto
        show "compPointers (Stack st') (Denvalue e\<^sub>v)" unfolding compPointers_def
        proof intros
          fix tp1 tp2 l1 l2 l1' l2' stl1 stl2
          assume a0:"(type.Storage tp1, l1) |\<in>| fmran (Denvalue e\<^sub>v) \<and>
       (type.Storage tp2, l2) |\<in>| fmran (Denvalue e\<^sub>v) \<and>
       (l1 = Stackloc l1' \<and> accessStore l1' (Stack st') = Some (KStoptr stl1) \<or> l1 = Storeloc stl1) \<and>
       (l2 = Stackloc l2' \<and> accessStore l2' (Stack st') = Some (KStoptr stl2) \<or> l2 = Storeloc stl2)"
          then obtain i1 i2 where iDefs:" (Denvalue e\<^sub>v) $$ i1 = Some (type.Storage tp1, l1)
                                  \<and> (Denvalue e\<^sub>v) $$ i2 = Some (type.Storage tp2, l2)" by blast
          then have "(type.Storage tp1, l1) |\<in>| fmran (Denvalue e') \<and> (type.Storage tp2, l2) |\<in>| fmran (Denvalue e')" using a0
            by (metis denLink fmlookup_ran_iff)
          then show "if TypedStoSubpref stl2 stl1 tp1 then CompStoType tp1 tp2 stl1 stl2
                else if TypedStoSubpref stl1 stl2 tp2 then CompStoType tp2 tp1 stl2 stl1 else True"
            using cpNew using a0 by blast
        qed
      next
        show "balanceTypes (Accounts st')" using IH1 unfolding StateInvariant_def TypeSafe_def by blast
      next
        have "envAddressesWellFormed e\<^sub>v" using 10(2) unfolding TypeSafe_def by simp
        then show "addressFormat (Address e\<^sub>v)" and "addressFormat (Sender e\<^sub>v)" by simp+
      next
        show "svalueTypes (Svalue e\<^sub>v)" using 10(2) unfolding TypeSafe_def by simp
      next
        show "lessThanTopLocs (Stack st')" using IH1 unfolding StateInvariant_def TypeSafe_def by blast
      next
        show "lessThanTopLocs cd" using 10(2) unfolding TypeSafe_def by simp
      next
        show "lessThanTopLocs (Memory st')" using IH1 unfolding StateInvariant_def TypeSafe_def by blast
      next
        have oldTC:"typeCompat (Denvalue e') (Stack st') (Memory st') (Storage st' (Address e')) cd'"
          using IH1 unfolding StateInvariant_def TypeSafe_def by blast
        show "typeCompat (Denvalue e\<^sub>v) (Stack st') (Memory st') (Storage st' (Address e\<^sub>v)) cd"
          unfolding typeCompat_def
        proof intros
          fix t l
          assume inDen:"(t, l) |\<in>| fmran (Denvalue e\<^sub>v)"
          then have inDenN:"(t, l) |\<in>| fmran (Denvalue e')"
            using denLink by (meson fmlookup_ran_iff)

          show "denvalueCon (Stack st') (Memory st') (Storage st' (Address e\<^sub>v)) cd t l"
          proof(cases l)
            case (Stackloc x1)
            then have oldTC':"(
             case accessStore x1 (Stack st') of None \<Rightarrow> False
              | Some (KValue val) \<Rightarrow> (case t of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
              | Some (KCDptr stloc) \<Rightarrow> (case t of Calldata struct \<Rightarrow> MCon struct cd' stloc | _ \<Rightarrow> False)
              | Some (KMemptr stloc) \<Rightarrow> (case t of type.Memory struct \<Rightarrow> MCon struct (Memory st') stloc | _ \<Rightarrow> False)
              | Some (KStoptr stloc) \<Rightarrow> (case t of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st' (Address e')) | _ \<Rightarrow> False))"
              using oldTC unfolding typeCompat_def using inDenN by fastforce
            then show ?thesis
            proof(cases "accessStore x1 (Stack st')")
              case None
              then show ?thesis using oldTC unfolding typeCompat_def using inDenN sameAdd Stackloc by fastforce
            next
              case (Some a)
              then show ?thesis
              proof(cases a)
                case (KValue x1')
                then show ?thesis using oldTC unfolding typeCompat_def using inDenN sameAdd Some Stackloc by force
              next
                case (KCDptr x2)
                then obtain struct where structDef:"t = Calldata struct \<and> MCon struct cd' x2"
                  using oldTC' unfolding typeCompat_def using inDenN sameAdd Some Stackloc by (cases t; auto)
                then show ?thesis using tsDecl KCDptr Some Stackloc sameCD by simp
              next
                case (KMemptr x3)
                then show ?thesis using oldTC unfolding typeCompat_def using inDenN sameAdd Some Stackloc by fastforce
              next
                case (KStoptr x4)
                then have "case t of type.Storage struct \<Rightarrow> SCon struct x4 (Storage st' (Address e')) | _ \<Rightarrow> False"
                  using oldTC' using inDenN sameAdd Some Stackloc by (auto split:option.splits type.splits stackvalue.splits denvalue.splits)
                then obtain struct where "t = type.Storage struct \<and> SCon struct x4 (Storage st' (Address e'))" by (cases t; auto)
                then show ?thesis using Some Stackloc KStoptr
                  by (simp add: sameAdd)
              qed
            qed
          next
            case (Storeloc x2)
            then show ?thesis using oldTC unfolding typeCompat_def using inDenN sameAdd
              by (metis (no_types, lifting) denvalue.simps(6) type.exhaust type.simps(17,18,19,20))
          qed
        qed
      next

        show "denvalueTypeCorrectness e\<^sub>v (Stack st') (Memory st')"
          unfolding denvalueTypeCorrectness_def
        proof intros
          fix t l ptr_loc sub_loc
          assume in1:"(type.Memory t, Stackloc l) |\<in>| fmran (Denvalue e\<^sub>v) \<and> accessStore l (Stack st') = Some (KMemptr ptr_loc)"
          then have in2:"(type.Memory t, Stackloc l) |\<in>| fmran (Denvalue e')" using denLink
            by (meson fmlookup_ran_iff)
          then show "(case t of MTArray len arr \<Rightarrow> \<forall>i<len. accessTypeStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (Memory st') = Some arr
        | MTValue val \<Rightarrow> accessTypeStore ptr_loc (Memory st') = Some (MTValue val))"
            using IH1 unfolding StateInvariant_def TypeSafe_def denvalueTypeCorrectness_def
            using in1 in2 by blast
        qed
      next
        show "subPrefixStructuralConsistency (Memory st')" using IH1 unfolding StateInvariant_def TypeSafe_def by blast
      next
        show "SomeValSomeTyp (Memory st')" using IH1 unfolding StateInvariant_def TypeSafe_def by blast
      qed

    next
      have fiOld:"
        \<exists>c ct dud.
          Type (Accounts st (Address e\<^sub>v)) = Some (atype.Contract c) \<and>
          Contract e\<^sub>v = c \<and>
          ep $$ c = Some (ct, dud) \<and>
          (\<forall>id v. (ct $$ id = Some (Var v)) = (Denvalue e\<^sub>v $$ id = Some (type.Storage v, Storeloc id))) \<and>
          (\<forall>id v loc. Denvalue e\<^sub>v $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc) \<and>
          (\<forall>t l p.
              (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e\<^sub>v) \<and> accessStore l (Stack st) = Some (KStoptr p) \<longrightarrow>
              (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e\<^sub>v) \<and> CompStoType t' t l' p))"
        using 10(4) unfolding fullyInitialised_def by blast
      then obtain c_fi ct_fi dud_fi where fiC:"
          Type (Accounts st (Address e\<^sub>v)) = Some (atype.Contract c_fi) \<and>
          Contract e\<^sub>v = c_fi \<and>
          ep $$ c_fi = Some (ct_fi, dud_fi) \<and>
          (\<forall>id v. (ct_fi $$ id = Some (Var v)) = (Denvalue e\<^sub>v $$ id = Some (type.Storage v, Storeloc id))) \<and>
          (\<forall>id v loc. Denvalue e\<^sub>v $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc)"
        and fiPtr:"\<forall>t l p.
              (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e\<^sub>v) \<and> accessStore l (Stack st) = Some (KStoptr p) \<longrightarrow>
              (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e\<^sub>v) \<and> CompStoType t' t l' p)"
        by blast
      have typeNew:"Type (Accounts st' (Address e\<^sub>v)) = Some (atype.Contract c_fi)"
        using fiC atype_same "10.prems"(2,3) statement_with_gas.atype_same statement_with_gas_axioms by blast
      have fiFinal:"fullyInitialised e' (Accounts st') (Stack st')"
        using IH1 unfolding StateInvariant_def by blast
      have ptrNew:"\<forall>t l p.
           (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e\<^sub>v) \<and> accessStore l (Stack st') = Some (KStoptr p) \<longrightarrow>
           (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e\<^sub>v) \<and> CompStoType t' t l' p)"
      proof (intro allI impI)
        fix t l p
        assume in1:"(type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e\<^sub>v) \<and> accessStore l (Stack st') = Some (KStoptr p)"
        have inNew:"(type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e')"
          using denLink in1 by (meson fmlookup_ran_iff)
        from fiFinal inNew in1 obtain t' l' where newPtr:
            "(type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e')"
            and comp:"CompStoType t' t l' p"
          unfolding fullyInitialised_def by blast
        from newPtr obtain iid where iidDef:"Denvalue e' $$ iid = Some (type.Storage t', Storeloc l')"
          using fmlookup_ran_iff by fast
        have oldLookup:"Denvalue e\<^sub>v $$ iid = Some (type.Storage t', Storeloc l')"
        proof (cases "iid = id0")
          case True
          have "\<forall>t l. Denvalue e' $$ id0 = Some (t, Storeloc l) \<longrightarrow> Denvalue e\<^sub>v $$ id0 = Some (t, Storeloc l)"
            using decl_env_storlocs_unchanged[OF 1(3)] by simp
          then show ?thesis using iidDef True by blast
        next
          case False
          then show ?thesis using decl_env_not_i[OF 1(3) iidDef] by blast
        qed
        have oldRan:"(type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e\<^sub>v)"
          using oldLookup by (meson fmranI)
        show "\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e\<^sub>v) \<and> CompStoType t' t l' p"
          using oldRan comp by blast
      qed
      show "fullyInitialised e\<^sub>v (Accounts st') (Stack st')"
        unfolding fullyInitialised_def using fiC fiPtr ptrNew typeNew by blast
    next
      fix locs t
      assume in1:"accessTypeStore locs (Memory st) = Some t"
      then have "\<exists>v. accessStore locs (Memory st) = Some v"
        using 10(2) unfolding TypeSafe_def SomeValSomeTyp_def by blast
      then obtain i where idef:"i < Toploc (Memory st) \<and> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t i) "
        using 10(2) unfolding TypeSafe_def lessThanTopLocs_def by blast
      then have same:"accessTypeStore locs (Memory st) = accessTypeStore locs mem'"
        using tsDecl unfolding ncpOMemInDMem_def by simp
      then have "accessTypeStore locs (Memory (st\<lparr>Gas := g, Stack := sck', Memory := mem'\<rparr>)) = Some t"
        using in1 by simp
      then show "accessTypeStore locs (Memory st') = Some t"
        using in1 IH1 unfolding StateInvariant_def by simp
    next
      fix locs v
      assume in1:"accessStore locs (Memory st) = Some (MPointer v)"
      then obtain i where idef:"i < Toploc (Memory st) \<and> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t i) "
        using 10(2) unfolding TypeSafe_def lessThanTopLocs_def by blast
      then have same:"accessStore locs (Memory st) = accessStore locs mem'"
        using tsDecl unfolding ncpOMemInDMem_def by simp
      then have "accessStore locs (Memory (st\<lparr>Gas := g, Stack := sck', Memory := mem'\<rparr>)) = Some (MPointer v)"
        using in1 by simp
      then show "\<exists>v'. accessStore locs (Memory st') = Some (MPointer v')"
        using in1 IH1 unfolding StateInvariant_def by simp
    next
      fix locs v
      assume in1:"accessStore locs (Memory st) = Some (MValue v)"
      then obtain i where idef:"i < Toploc (Memory st) \<and> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t i) "
        using 10(2) unfolding TypeSafe_def lessThanTopLocs_def by blast
      then have same:"accessStore locs (Memory st) = accessStore locs mem'"
        using tsDecl unfolding ncpOMemInDMem_def by simp
      then have "accessStore locs (Memory (st\<lparr>Gas := g, Stack := sck', Memory := mem'\<rparr>)) = Some (MValue v)"
        using in1 by simp
      then show "\<exists>v'. accessStore locs (Memory st') = Some (MValue v')"
        using in1 IH1 unfolding StateInvariant_def by simp
    next
      fix i loc
      assume in1:"i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) "
        and in2:" accessStore loc (Memory st) = None"
      then have same:"accessStore loc (Memory st) = accessStore loc mem'"
        using tsDecl unfolding ncpOMemInDMem_def by simp
      moreover have "Toploc (Memory st) \<le> Toploc mem'" using tsDecl unfolding ncpOMemInDMem_def by simp
      moreover have "i < Toploc (Memory (st\<lparr>Gas := g, Stack := sck', Memory := mem'\<rparr>)) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)"
        using calculation in1 by auto
      ultimately have "accessStore loc (Memory (st\<lparr>Gas := g, Stack := sck', Memory := mem'\<rparr>)) = None \<longrightarrow>
        accessStore loc (Memory st') = None" using IH1 unfolding StateInvariant_def by simp
      then show "accessStore loc (Memory st') = None" using in2 same by simp

    next
      show "Toploc (Memory st) \<le> Toploc (Memory st')"
        using 1 IH1 unfolding StateInvariant_def using tsDecl by simp
    qed
  qed
next
  case (11 i xe val e cd st)
  show ?case
  proof(cases rule:new[OF 11(3)])
    case (1 v t g ct cn fb e\<^sub>l cd\<^sub>l k\<^sub>l m\<^sub>l g' acc st'' v')
    then have a10:"assert Gas (\<lambda>st. costs (NEW i xe val) e cd st < state.Gas st) st = Normal ((), st)" by simp
    let ?sgas = "st\<lparr>Gas := state.Gas st - costs (NEW i xe val) e cd st\<rparr>"
    have a20:"modify (\<lambda>st. st\<lparr>Gas := state.Gas st - costs (NEW i xe val) e cd st\<rparr>) st = Normal ((), ?sgas)" by simp
    let ?newAdd = "hash_version (Address e) (ShowL\<^sub>n\<^sub>a\<^sub>t (Contracts (Accounts ?sgas (Address e))))"
    have notSame:"(Address e) \<noteq> ?newAdd"
      by (metis hash_version_inequality)
    have formatAdd:"addressFormat (hash_version (Address e) (ShowL\<^sub>n\<^sub>a\<^sub>t (Contracts (Accounts (st\<lparr>Gas := state.Gas st - costs (NEW i xe val) e cd st\<rparr>) (Address e)))))"
      unfolding addressFormat_def typeCon.simps
    proof -
      have "CHR ''.'' \<notin> set (literal.explode (Address e))"
        using 11(2) unfolding TypeSafe_def addressFormat_def typeCon.simps checkAddress_def by blast
      then have "CHR ''.'' \<notin> set (literal.explode (STR ''-'' + Address e))"
        by (simp add: Literal.rep_eq add_Literal_assoc)
      moreover have "CHR ''.'' \<notin> set (literal.explode (ShowL\<^sub>n\<^sub>a\<^sub>t (Contracts (Accounts (st\<lparr>Gas := state.Gas st - costs (NEW i xe val) e cd st\<rparr>) (Address e)))))"
        using ShowLNatDot by blast

      ultimately have "CHR ''.'' \<notin> set
                      (literal.explode ((ShowL\<^sub>n\<^sub>a\<^sub>t (Contracts (Accounts (st\<lparr>Gas := state.Gas st - costs (NEW i xe val) e cd st\<rparr>) (Address e))))
                      + (STR ''-'' + Address e)))"
        by (simp add: plus_literal.rep_eq)
      then show "checkAddress (hash_version (Address e) (ShowL\<^sub>n\<^sub>a\<^sub>t (Contracts (Accounts (st\<lparr>Gas := state.Gas st - costs (NEW i xe val) e cd st\<rparr>) (Address e)))))"
        unfolding checkAddress_def hash_version_def by blast
    qed
    let ?updState = "st\<lparr>Gas := g, Accounts := (Accounts st)((?newAdd) := \<lparr>Bal = ShowL\<^sub>i\<^sub>n\<^sub>t 0, Type = Some (atype.Contract i), Contracts = 0\<rparr>),
                                                Storage := (Storage st)((?newAdd) := {$$})\<rparr>"
    obtain uus where uusDef:"uus = ?updState" by blast
    have sameUpd:"Memory ?updState = Memory st \<and> Stack ?updState = Stack st" by auto
    have a30:"applyf (\<lambda>st. hash_version (Address e) (ShowL\<^sub>n\<^sub>a\<^sub>t (Contracts (Accounts st (Address e))))) (?sgas)
                    = Normal (hash_version (Address e) (ShowL\<^sub>n\<^sub>a\<^sub>t (Contracts (Accounts ?sgas (Address e)))) , (?sgas))" using 1 by auto
    have a40:" assert Err (\<lambda>st. Type (Accounts st ?newAdd) = None) (?sgas)
                          = Normal ((), ?sgas)" using 1 by simp
    have a50:"toState (local.expr val e cd) (?sgas) = Normal ((KValue v, Value t), st\<lparr>Gas := g\<rparr>)" using 1 by auto
    have a60:"(case (KValue v, Value t) of (KValue v, Value t) \<Rightarrow> return (v, t) | (KValue v, _) \<Rightarrow> throw Err
                  | (_, b) \<Rightarrow> throw Err) (st\<lparr>Gas := g\<rparr>) = Normal ((v,t), st\<lparr>Gas := g\<rparr>)" using 1 by simp
    have a65:"option Err (\<lambda>_. convert t (TUInt b256) v) (st\<lparr>Gas := g\<rparr>) = Normal (v', st\<lparr>Gas := g\<rparr>)" using 1 by simp
    have a70:"option Err (\<lambda>_. ep $$ i) (st\<lparr>Gas := g\<rparr>) = Normal ((ct, cn, fb), st\<lparr>Gas := g\<rparr>)" using 1 by simp
    obtain folded where a80: "folded = ffold_init ct (emptyEnv (?newAdd) i (Address e) v') (fmdom ct)"
      using 1 by blast
    have a90:"toState (local.load True (fst cn) xe folded emptyTypedStore emptyStore emptyTypedStore e cd) ?updState = Normal ((e\<^sub>l,
        cd\<^sub>l, k\<^sub>l, m\<^sub>l), ?updState\<lparr>Gas := g'\<rparr>)"
      using 1 a80 by simp


    have a110:" option Err (\<lambda>st. transfer (Address e) ?newAdd v' (Accounts st)) (?updState\<lparr>Gas:=g'\<rparr>) = Normal (acc, ?updState\<lparr>Gas:=g'\<rparr>)"
      using 1 by auto
    have a120:"applyf (\<lambda>st. (Stack st, Memory st)) (?updState\<lparr>Gas:=g'\<rparr>) = Normal ((Stack st, Memory st), ?updState\<lparr>Gas:=g'\<rparr>)"
      by simp
    have a130:"modify (\<lambda>st'. st'\<lparr>Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>) (?updState \<lparr>Gas:=g'\<rparr>)
              = Normal ((), ?updState\<lparr>Gas:=g', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)"
      by simp

    have BtUus:"balanceTypes (Accounts uus)"
      unfolding balanceTypes_def
    proof intros
      fix adv
      show "typeCon (TUInt b256) (Bal (Accounts uus adv)) "
      proof(cases "adv = ?newAdd")
        case True
        then have " (Bal (Accounts uus adv)) = (ShowL\<^sub>i\<^sub>n\<^sub>t 0)" using uusDef by simp
        then show ?thesis unfolding typeCon.simps checkUInt_def
          using Read_ShowL_id by presburger
      next
        case False
        then have "(Bal (Accounts uus adv)) = (Bal (Accounts st adv))" using uusDef by simp
        then show ?thesis using 11(2) unfolding TypeSafe_def balanceTypes_def by simp
      qed
    qed

    have svv':"svalueTypes v'" unfolding svalueTypes_def
      using 1(4,3) 11(2) 11(4)
      using exprTypeconInduct(3)[of ]
        typeSafeConvert[of t v "(TUInt b256)"] convertSame by fastforce

    have btACC:"balanceTypes acc" unfolding balanceTypes_def
    proof -
      have old:"balanceTypes (Accounts (uus))" using BtUus by simp
      have accExp:"(case subBalance (Address e) v' (Accounts (uus)) of None \<Rightarrow> None | Some x \<Rightarrow> addBalance ?newAdd v' x) = Some acc"
        using 1(7) uusDef unfolding transfer_def by simp
      have v'TC: "typeCon (TUInt b256) v'"
        using svv' unfolding svalueTypes_def by blast

      show "\<forall>adv'. typeCon (TUInt b256) (Bal (acc adv')) "
      proof(cases "?newAdd = (Address e)")
        case same:True
        then show ?thesis using notSame by simp
      next
        case notSame:False
        show ?thesis
        proof
          fix adv'
          show "typeCon (TUInt b256) (Bal (acc adv')) "
          proof(cases "adv' = (Address e)")
            case True

            then have tco:"typeCon (TUInt b256) (Bal ((Accounts uus) adv'))"
              using True old accExp balanceTypes_def by blast
            have "Bal (acc (Address e)) = ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts (uus) (Address e))) - (ReadL\<^sub>i\<^sub>n\<^sub>t v'))"
              using transfer_subRead[OF _ _ v'TC ] 1(7) uusDef True notSame tco by auto
            then show ?thesis using True
              using "1"(7,3) Read_ShowL_id tco checkUInt_def transfer_val1 transfer_val2
              by (metis transfer_Bal_typeCon[unfolded transfer_def, OF accExp] old[unfolded balanceTypes_def])

          next
            case False
            then show ?thesis
            proof(cases "adv' = ?newAdd")
              case True
              then have tco:"typeCon (TUInt b256) (Bal ((Accounts uus) ?newAdd))"
                using True old accExp balanceTypes_def by simp
              then have "Bal (acc ?newAdd) = (ShowL\<^sub>i\<^sub>n\<^sub>t ((ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts (uus) ?newAdd))) + (ReadL\<^sub>i\<^sub>n\<^sub>t v')))"
                using transfer_addRead[OF 1(7)_ v'TC ] 1(3) notSame uusDef by auto
              moreover have "typeCon (TUInt b256) (ShowL\<^sub>i\<^sub>n\<^sub>t ((ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (Accounts (uus) ?newAdd))) + (ReadL\<^sub>i\<^sub>n\<^sub>t v')))"
                using "1"(7,3) Read_ShowL_id tco checkUInt_def transfer_val1 transfer_val2 transfer_val3
                using transfer_Bal_typeCon[unfolded transfer_def, OF accExp] old calculation unfolding balanceTypes_def by metis
              ultimately show ?thesis using True by simp
            next
              case f2:False
              show ?thesis using transfer_eq[OF 1(7) False f2] old
                using balanceTypes_def uusDef by simp
            qed
          qed
        qed
      qed
    qed

    obtain ii :: environment where iiDef: "i = Contract ii" using 1
      by (metis Environment.select_convs(2))
    have epA:"ep $$ Contract ii = Some (ct, cn, fb)" using 1 iiDef by blast
    have atUus:"AddressTypes (Accounts uus)"
      unfolding AddressTypes_def
    proof intros
      fix adv
      show "case Type (Accounts uus adv) of None \<Rightarrow> True | Some EOA \<Rightarrow> True | Some (atype.Contract c) \<Rightarrow> addressFormat adv \<and> c |\<in>| fmdom ep "
      proof(cases "Type (Accounts uus adv)")
        case None
        then show ?thesis by simp
      next
        case (Some a)
        then show ?thesis
        proof(cases a)
          case EOA
          then show ?thesis using Some by simp
        next
          case (Contract x2)
          then show ?thesis
          proof(cases "adv = ?newAdd")
            case True
            then have "Type (Accounts uus adv) = Some (atype.Contract i)" using uusDef by auto
            then have "i = x2" using Some Contract by simp
            moreover have "ep $$ i = Some (ct, cn, fb)" using epA iiDef by simp
            moreover have "addressFormat adv" using iiDef epA formatAdd True by simp
            ultimately show ?thesis using Some Contract
              by (metis Option.option.simps(5) atype.simps(5) fmlookup_dom_iff)
          next
            case False
            then have "(Accounts uus adv) = Accounts st adv" using uusDef by simp
            then show ?thesis using 11(2) unfolding TypeSafe_def AddressTypes_def using Some Contract
              by metis
          qed
        qed
      qed
    qed
    have scUus:"safeContract (Accounts uus) (Storage uus)"
      unfolding safeContract_def
    proof intros
      fix e' ct' dud' i' tp
      assume in1:"Type (Accounts uus (Address (e'::environment))) = Some (atype.Contract (Contract e')) \<and>
                 ep $$ Contract (e'::environment) = Some (ct', dud') \<and>
                 ct' $$ i' = Some (Var tp)"
      show "SCon tp i' (Storage uus (Address e'))"
      proof(cases "Address e' = ?newAdd")
        case True
        then have "(Storage uus (Address e')) = {$$}" using uusDef by simp
        then show ?thesis
        proof(induction tp arbitrary:i')
          case (STArray x1 tp)
          then show ?case by simp
        next
          case (STMap x1 tp)
          then show ?case by simp
        next
          case (STValue x)
          have "typeCon x (ival x)" by (simp add: ivalTypeCon)
          then show ?case unfolding SCon.simps accessStorage_def using STValue by simp
        qed
      next
        case False
        then have "Storage uus (Address e') = Storage st (Address e')"
          using uusDef by simp
        moreover have "Type (Accounts st (Address e')) = Some (atype.Contract (Contract e'))"
          using False in1 uusDef by simp
        moreover have "ep $$ Contract (e'::environment) = Some (ct', dud')"
          using in1 by simp
        moreover have "ct' $$ i' = Some (Var tp)"
          using in1 by simp
        moreover have "safeContract (Accounts st) (Storage st)"
          using 11(2) unfolding TypeSafe_def by simp
        ultimately show ?thesis
          unfolding safeContract_def
          by presburger
      qed
    qed
    have cohUus:"Type (Accounts uus ?newAdd) = Some (atype.Contract (Contract ii))"
      using uusDef iiDef by simp
    have TSInit:"\<forall>x y. TypeSafe folded (Accounts uus)
                  emptyStore emptyTypedStore (Storage uus) emptyTypedStore \<and>
       (Denvalue folded $$ x = Some y \<longrightarrow> snd y = Storeloc x) \<and> (Denvalue folded $$ x = Some y \<longrightarrow>
           (\<exists>t1. ct $$ x = Some (Var t1) \<and> fst y = type.Storage t1))"
    proof -
      have "safeContract (Accounts uus) (Storage uus)" using scUus by simp
      moreover have "balanceTypes (Accounts uus)" using BtUus by simp
      moreover have "svalueTypes v'"
      proof -
        have "typeCon t (extractValueType (KValue v))"
          using 1(4,3) 11(2) 11(4)
          using exprTypeconInduct(3)[of val e cd "(st\<lparr>Gas := state.Gas st - costs (NEW i xe val) e cd st\<rparr>)" "(state.Gas
              (st\<lparr>Gas := state.Gas st - costs (NEW i xe val) e cd st\<rparr>))" "KValue v" "Value t" g]
            typeSafeConvert[of t v "(TUInt b256)"] convertSame by simp
        then show ?thesis unfolding svalueTypes_def using 1(3) a65
          by (metis "1"(4) convertSame extractValueType.simps(1) typeSafeConvert)
      qed
      moreover have "lessThanTopLocs emptyStore" using emptyTopLocs by simp
      moreover have "ep $$ Contract ii = Some (ct, cn, fb)" using epA by simp
      moreover have "addressFormat (?newAdd)" using formatAdd by simp
      moreover have "addressFormat (Address e)" using 11(2) unfolding TypeSafe_def by simp
      moreover have "AddressTypes (Accounts uus)" using atUus by simp
      moreover have sp:"subPrefixStructuralConsistency emptyTypedStore" unfolding subPrefixStructuralConsistency_def accessTypeStore_def emptyTypedStore_def by simp
      moreover have "SomeValSomeTyp emptyTypedStore" unfolding SomeValSomeTyp_def accessTypeStore_def accessStore_def emptyTypedStore_def by auto
      moreover have "Type (Accounts uus ?newAdd) = Some (atype.Contract (Contract ii))" using cohUus by simp

      ultimately show "\<forall>x y. TypeSafe folded (Accounts uus)
                  emptyStore emptyTypedStore (Storage uus) emptyTypedStore \<and>
       (Denvalue folded $$ x = Some y \<longrightarrow> snd y = Storeloc x) \<and> (Denvalue folded $$ x = Some y \<longrightarrow>
           (\<exists>t1. ct $$ x = Some (Var t1) \<and> fst y = type.Storage t1))"
        using a80 unfolding ffold_init_def
        using ffoldInitTypeSafe[of "Accounts uus" "Storage uus" v' emptyTypedStore ii ct "(cn, fb)" ?newAdd "Address e" "fmdom ct"]
        using iiDef typedEmptyTopLocs by blast
    qed
    have a140:"TypeSafe e\<^sub>l (Accounts (uus\<lparr>Gas:=g', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>))
                            (Stack (uus\<lparr>Gas:=g', Accounts := acc, Stack := k\<^sub>l, Memory :=m\<^sub>l\<rparr>))
                            (Memory (uus\<lparr>Gas:=g', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>))
                            (Storage (uus\<lparr>Gas:=g', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>))
                            cd\<^sub>l \<and> fullyInitialised e\<^sub>l acc k\<^sub>l"
    proof -

      have aa1:"load True (fst cn) xe folded emptyTypedStore emptyStore emptyTypedStore e cd ?updState g =
    Normal ((e\<^sub>l, cd\<^sub>l, k\<^sub>l, m\<^sub>l), g')" using 1(6) a80 unfolding ffold_init_def by simp
      moreover have tsE:"TypeSafe e (Accounts uus) (Stack uus) (Memory uus) (Storage uus) cd"
        unfolding TypeSafe_def
      proof intros
        show "AddressTypes (Accounts uus)" using atUus by simp
      next
        show "safeContract (Accounts uus) (Storage uus)" using scUus by simp
      next
        show "unique_locations (Denvalue e)" using 11(2) unfolding TypeSafe_def by simp
      next

        show "compPointers (Stack uus) (Denvalue e)"
          using 11(2) unfolding TypeSafe_def
          using sameUpd uusDef by argo
      next
        show "balanceTypes (Accounts uus)" using BtUus by simp
      next
        have "envAddressesWellFormed e" using 11(2) sameUpd uusDef unfolding TypeSafe_def by simp
        then show "addressFormat (Address e)" and "addressFormat (Sender e)" by simp+
      next
        show "svalueTypes (Svalue e)" using 11(2) sameUpd uusDef unfolding TypeSafe_def by simp
      next
        show "lessThanTopLocs (Stack uus)" using 11(2) sameUpd uusDef unfolding TypeSafe_def by auto
      next
        show "lessThanTopLocs cd" using 11(2) sameUpd uusDef unfolding TypeSafe_def by auto
      next
        show "lessThanTopLocs (Memory uus)" using 11(2) sameUpd uusDef unfolding TypeSafe_def by auto
      next
        have tcOld:"typeCompat (Denvalue e) (Stack st) (Memory st) (Storage st (Address e)) cd"
          using 11(2) unfolding TypeSafe_def by blast
        show "typeCompat (Denvalue e) (Stack uus) (Memory uus) (Storage uus (Address e)) cd"
          unfolding typeCompat_def
        proof intros
          fix t l
          assume inDen:"(t, l) |\<in>| fmran (Denvalue e)"

          show "denvalueCon (Stack uus) (Memory uus) (Storage uus (Address e)) cd t l"
          proof(cases l)
            case (Stackloc x1)
            have tcOld':"case accessStore x1 (Stack st) of None \<Rightarrow> False
                         | Some (KValue val) \<Rightarrow> (case t of Value typ \<Rightarrow> typeCon typ val | _ \<Rightarrow> False)
                         | Some (KCDptr stloc) \<Rightarrow> (case t of Calldata struct \<Rightarrow> MCon struct cd stloc | _ \<Rightarrow> False)
                         | Some (KMemptr stloc) \<Rightarrow> (case t of type.Memory struct \<Rightarrow> MCon struct (Memory st) stloc | _ \<Rightarrow> False)
                         | Some (KStoptr stloc) \<Rightarrow> (case t of type.Storage struct \<Rightarrow> SCon struct stloc (Storage st (Address e)) | _ \<Rightarrow> False)"
              using sameUpd Stackloc inDen tcOld unfolding typeCompat_def by force
            then show ?thesis
            proof(cases "accessStore x1 (Stack uus)")
              case None
              then show ?thesis using tcOld' sameUpd uusDef by simp
            next
              case (Some a)
              then show ?thesis
              proof(cases a)
                case (KValue x1')
                then show ?thesis using tcOld' sameUpd uusDef Some Stackloc by simp
              next
                case (KCDptr x2)

                then show ?thesis using tcOld' sameUpd uusDef Some Stackloc by simp
              next
                case (KMemptr x3)
                then show ?thesis using tcOld' sameUpd uusDef Some Stackloc by (cases t; fastforce)
              next
                case (KStoptr x4)

                then show ?thesis
                proof(cases "Address e = ?newAdd")
                  case True
                  then have empt:"Storage uus (Address e) = {$$}" using uusDef by simp
                  then obtain struct where struct_def:"t = type.Storage struct"
                    using tcOld' sameUpd uusDef Some Stackloc KStoptr by (cases t; fastforce)
                  have "SCon struct x4 (Storage uus (Address e))"
                  proof(induction struct arbitrary:x4)
                    case (STArray x1 tp)
                    then show ?case by simp
                  next
                    case (STMap x1 tp)
                    then show ?case by simp
                  next
                    case (STValue x)
                    have "typeCon x (ival x)" by (simp add: ivalTypeCon)
                    then show ?case unfolding SCon.simps accessStorage_def using STValue empt by simp
                  qed
                  then show ?thesis using tcOld' sameUpd uusDef Some Stackloc KStoptr struct_def by simp
                next
                  case False
                  then have "Storage uus (Address e) = Storage st (Address e)" using uusDef by simp
                  then show ?thesis using tcOld' sameUpd uusDef Some Stackloc KStoptr by (cases t; fastforce)
                qed
              qed
            qed
          next
            case (Storeloc x2)
            then show ?thesis
            proof(cases "Address e = ?newAdd")
              case True
              then have empt:"Storage uus (Address e) = {$$}" using uusDef by simp
              then obtain struct where struct_def:"t = type.Storage struct"
                using sameUpd uusDef Storeloc tcOld inDen unfolding typeCompat_def by (cases t; fastforce)
              have "SCon struct x2 (Storage uus (Address e))"
              proof(induction struct arbitrary:x2)
                case (STArray x1 tp)
                then show ?case by simp
              next
                case (STMap x1 tp)
                then show ?case by simp
              next
                case (STValue x)
                have "typeCon x (ival x)" by (simp add: ivalTypeCon)
                then show ?case unfolding SCon.simps accessStorage_def using STValue empt by simp
              qed
              then show ?thesis using tcOld inDen unfolding typeCompat_def using sameUpd uusDef Storeloc struct_def by simp
            next
              case False
              then have "Storage uus (Address e) = Storage st (Address e)" using uusDef by simp
              then show ?thesis using tcOld inDen unfolding typeCompat_def using sameUpd uusDef Storeloc by (cases t; fastforce)
            qed
          qed
        qed
      next
        show "denvalueTypeCorrectness e (Stack uus) (Memory uus)" using uusDef using 11(2) unfolding TypeSafe_def by simp
      next
        show "subPrefixStructuralConsistency (Memory uus)" using uusDef using 11(2) unfolding TypeSafe_def by simp
      next
        show "SomeValSomeTyp (Memory uus)" using uusDef using 11(2) unfolding TypeSafe_def by simp
      qed

      moreover have "TypeSafe folded (Accounts uus) emptyStore emptyTypedStore (Storage uus) emptyTypedStore" using TSInit
        by blast

      moreover have a6:"fullyInitialised e (Accounts uus) (Stack uus)"
      proof -
        have fiOld:"
          \<exists>c ct dud.
            Type (Accounts st (Address e)) = Some (atype.Contract c) \<and>
            Contract e = c \<and>
            ep $$ c = Some (ct, dud) \<and>
            (\<forall>id v. (ct $$ id = Some (Var v)) = (Denvalue e $$ id = Some (type.Storage v, Storeloc id))) \<and>
            (\<forall>id v loc. Denvalue e $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc) \<and>
            (\<forall>t l p.
                (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l (Stack st) = Some (KStoptr p) \<longrightarrow>
                (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e) \<and> CompStoType t' t l' p))"
          using 11(4) unfolding fullyInitialised_def by blast
        then obtain c_fi ct_fi dud_fi where fiC:"
            Type (Accounts st (Address e)) = Some (atype.Contract c_fi) \<and>
            Contract e = c_fi \<and>
            ep $$ c_fi = Some (ct_fi, dud_fi) \<and>
            (\<forall>id v. (ct_fi $$ id = Some (Var v)) = (Denvalue e $$ id = Some (type.Storage v, Storeloc id))) \<and>
            (\<forall>id v loc. Denvalue e $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc)"
          and fiPtr:"\<forall>t l p.
                (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l (Stack st) = Some (KStoptr p) \<longrightarrow>
                (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e) \<and> CompStoType t' t l' p)"
          by blast
        have typeNew:"Type (Accounts uus (Address e)) = Some (atype.Contract c_fi)"
          using fiC uusDef notSame by simp
        have ptrNew:"\<forall>t l p.
            (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l (Stack uus) = Some (KStoptr p) \<longrightarrow>
            (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e) \<and> CompStoType t' t l' p)"
          using fiPtr sameUpd uusDef by simp
        show ?thesis
          unfolding fullyInitialised_def using fiC typeNew ptrNew by blast
      qed

      have contractL:"Contract folded = Contract ii" using a80 iiDef by simp

      have ctd:"ep $$ Contract folded = Some (ct, cn, fb)" using a50 contractL 1 a10 iiDef by metis
      then have fi2:"\<forall>id v. (Denvalue folded $$ id = Some (type.Storage v, Storeloc id)) = (ct $$ id = Some (Var v))"
        using a80 unfolding ffold_init_def using ffoldInit_var_storage_mapping_eq[of ct ?newAdd i "(Address e)" v' folded] by auto
      moreover have "fullyInitialised e (Accounts ?updState) (Stack ?updState)" using a6 uusDef by blast
      moreover have fiFolded:"fullyInitialised folded (Accounts uus) emptyStore"
      proof -
        obtain c_fi where cfi:
          "Type (Accounts uus (Address folded)) = Some (atype.Contract c_fi) \<and> Contract folded = c_fi"
          using a80 11(4) uusDef unfolding fullyInitialised_def by simp
        obtain dud_fi where epfi:"ep $$ Contract folded = Some (ct, dud_fi)"
          using ctd by blast
        have mapfi:"\<forall>id v. (ct $$ id = Some (Var v)) = (Denvalue folded $$ id = Some (type.Storage v, Storeloc id))"
          using fi2 by blast
        have locfi:"\<forall>id v loc. Denvalue folded $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc"
        proof (intro allI impI)
          fix id v loc
          assume h:"Denvalue folded $$ id = Some (type.Storage v, Storeloc loc)"
          have hloc:"Denvalue folded $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> snd (type.Storage v, Storeloc loc) = Storeloc id"
            using TSInit by blast
          then show "id = loc" using h by simp
        qed
        have ptrfi:"\<forall>t l p.
            (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue folded) \<and> accessStore l emptyStore = Some (KStoptr p) \<longrightarrow>
            (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue folded) \<and> CompStoType t' t l' p)"
          by (simp add: accessStore_def emptyStore_def)
        show ?thesis
          unfolding fullyInitialised_def using cfi epfi mapfi locfi ptrfi by blast
      qed

      ultimately have exprTS:" TypeSafe e\<^sub>l (Accounts ?updState) k\<^sub>l m\<^sub>l (Storage ?updState) cd\<^sub>l \<and>
    fullyInitialised e\<^sub>l (Accounts ?updState) k\<^sub>l \<and> fullyInitialised e\<^sub>l
     (Accounts ?updState) k\<^sub>l"
        using exprTypeconInduct(4)[of True "fst cn" xe folded emptyTypedStore emptyStore
            emptyTypedStore e cd ?updState g e\<^sub>l cd\<^sub>l k\<^sub>l m\<^sub>l g'] uusDef by blast

      have cc1:"TypeSafe e\<^sub>l (acc) (k\<^sub>l) (m\<^sub>l) (Storage (uus)) cd\<^sub>l"
        unfolding TypeSafe_def
      proof intros
        show "AddressTypes acc" unfolding AddressTypes_def using tsE unfolding TypeSafe_def AddressTypes_def using 1(7) transfer_type_same uusDef by simp
      next
        have trUus:"transfer (Address e) ?newAdd v' (Accounts uus) = Some acc"
          using 1(7) uusDef by simp
        have scUus':"safeContract (Accounts uus) (Storage uus)"
          using tsE unfolding TypeSafe_def by simp
        show "safeContract acc (state.Storage uus)"
        proof (unfold safeContract_def, intro allI impI)
          fix env ct' dud' i' tp
          assume in1:"Type (acc (Address (env::environment))) = Some (atype.Contract (Contract env)) \<and>
                     ep $$ Contract env = Some (ct', dud') \<and>
                     ct' $$ i' = Some (Var tp)"
          have typeOld:"Type (Accounts uus (Address env)) = Some (atype.Contract (Contract env))"
            using in1 transfer_type_same[OF trUus, of "Address env"] by simp
          show "SCon tp i' (state.Storage uus (Address env))"
            using scUus' in1 typeOld unfolding safeContract_def by blast
        qed
      next
        show "unique_locations (Denvalue e\<^sub>l)" using exprTS unfolding TypeSafe_def by blast
      next
        show "compPointers k\<^sub>l (Denvalue e\<^sub>l)" using exprTS unfolding TypeSafe_def by blast
      next
        show "balanceTypes acc" using btACC by auto
      next
        have "envAddressesWellFormed e\<^sub>l" using exprTS unfolding TypeSafe_def by blast
        then show "addressFormat (Address e\<^sub>l)" and "addressFormat (Sender e\<^sub>l)" by simp+
      next
        show "svalueTypes (Svalue e\<^sub>l)" using exprTS unfolding TypeSafe_def by blast
      next
        show " lessThanTopLocs k\<^sub>l" using exprTS unfolding TypeSafe_def by blast
      next
        show " lessThanTopLocs cd\<^sub>l" using exprTS unfolding TypeSafe_def by blast
      next
        show "lessThanTopLocs m\<^sub>l" using exprTS unfolding TypeSafe_def by blast
      next
        show "typeCompat (Denvalue e\<^sub>l) k\<^sub>l m\<^sub>l (Storage uus (Address e\<^sub>l)) cd\<^sub>l" using uusDef exprTS unfolding TypeSafe_def by blast
      next
        show "denvalueTypeCorrectness e\<^sub>l k\<^sub>l m\<^sub>l" using TypeSafe_def exprTS by blast
      next
        show "subPrefixStructuralConsistency m\<^sub>l" using TypeSafe_def exprTS by blast
      next
        show "SomeValSomeTyp m\<^sub>l" using TypeSafe_def exprTS by blast
      qed

      have elFolded:"Address e\<^sub>l = Address folded \<and> Contract e\<^sub>l = Contract folded" using 1 a80
        using msel_ssel_expr_load_rexp_gas(4) aa1 by blast
      have cc2:"fullyInitialised e\<^sub>l acc k\<^sub>l"
      proof -
        have fiOld:"
          \<exists>c ct dud.
            Type (Accounts ?updState (Address e\<^sub>l)) = Some (atype.Contract c) \<and>
            Contract e\<^sub>l = c \<and>
            ep $$ c = Some (ct, dud) \<and>
            (\<forall>id v. (ct $$ id = Some (Var v)) = (Denvalue e\<^sub>l $$ id = Some (type.Storage v, Storeloc id))) \<and>
            (\<forall>id v loc. Denvalue e\<^sub>l $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc) \<and>
            (\<forall>t l p.
                (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e\<^sub>l) \<and> accessStore l k\<^sub>l = Some (KStoptr p) \<longrightarrow>
                (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e\<^sub>l) \<and> CompStoType t' t l' p))"
          using exprTS unfolding fullyInitialised_def by blast
        then obtain c_fi ct_fi dud_fi where fiC:"
            Type (Accounts ?updState (Address e\<^sub>l)) = Some (atype.Contract c_fi) \<and>
            Contract e\<^sub>l = c_fi \<and>
            ep $$ c_fi = Some (ct_fi, dud_fi) \<and>
            (\<forall>id v. (ct_fi $$ id = Some (Var v)) = (Denvalue e\<^sub>l $$ id = Some (type.Storage v, Storeloc id))) \<and>
            (\<forall>id v loc. Denvalue e\<^sub>l $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc)"
          and fiPtr:"\<forall>t l p.
              (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e\<^sub>l) \<and> accessStore l k\<^sub>l = Some (KStoptr p) \<longrightarrow>
              (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e\<^sub>l) \<and> CompStoType t' t l' p)"
          by blast
        have typeNew:"Type (acc (Address e\<^sub>l)) = Some (atype.Contract c_fi)"
          using fiC 1(7) transfer_type_same uusDef by simp
        show ?thesis
          unfolding fullyInitialised_def using fiC fiPtr typeNew by blast
      qed

      then show "TypeSafe e\<^sub>l (Accounts (uus\<lparr>Gas:=g',Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)) (Stack
          (uus\<lparr>Gas:=g',Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>))
     (Memory (uus\<lparr>Gas:=g',Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)) (Storage (uus\<lparr>Gas:=g',Accounts :=
         acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)) cd\<^sub>l
\<and> fullyInitialised e\<^sub>l acc k\<^sub>l"
        using cc1 by auto
    qed
    have a140':"TypeSafe e\<^sub>l (Accounts (?updState\<lparr>Gas:=g',Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>))
        (Stack (?updState\<lparr>Gas:=g',Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>))
   (Memory (?updState\<lparr>Gas:=g',Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)) (Storage
       (?updState\<lparr>Gas:=g',Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>)) cd\<^sub>l"
      using a140 uusDef by auto
    have "st\<lparr>Gas := g', Accounts := (Accounts st)((?newAdd) := \<lparr>Bal = ShowL\<^sub>i\<^sub>n\<^sub>t 0, Type = Some (atype.Contract i), Contracts = 0\<rparr>),
                                                Storage := (Storage st)((?newAdd) := {$$})\<rparr>
= (?updState\<lparr>Gas := g'\<rparr>)" by simp
    then have a18Exp:"local.stmt (snd cn) e\<^sub>l cd\<^sub>l
     (?updState\<lparr>Gas := g', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>) = Normal ((), st'')" using 1(8) by argo
    have a150:"fullyInitialised e\<^sub>l acc k\<^sub>l" using a140 by simp


    have IH1:" StateInvariant e\<^sub>l (?updState\<lparr>Gas:=g',Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>) st'' cd\<^sub>l"
      using 11(1)[OF a10 a20 a30 a40 a50 a60 _ a65 a70 _ _ _ a80 a90 _ _ _ a110 a120 _ a130 a140' a18Exp] a30 1(8) a150 by simp

    have st'Final:"st' = incrementAccountContracts (Address e) (st''\<lparr>Stack := Stack st, Memory := Memory st\<rparr>)" using 1 by blast

    then have sameStores:"Memory st = Memory st' \<and> Stack st = Stack st'" using 1 by simp
    show ?thesis unfolding StateInvariant_def
    proof intros
      show "TypeSafe e (Accounts st') (Stack st') (Memory st') (Storage st') cd" unfolding TypeSafe_def
      proof intros
        have old:"AddressTypes (Accounts st'')" using IH1 unfolding StateInvariant_def TypeSafe_def by auto
        show "AddressTypes (Accounts st')" using old unfolding AddressTypes_def using st'Final by fastforce

      next
        have scOld:"safeContract (Accounts st'') (Storage st'')"
          using IH1 unfolding StateInvariant_def TypeSafe_def by blast
        show "safeContract (Accounts st') (Storage st')"
        proof (unfold safeContract_def, intro allI impI)
          fix env ct' dud' i' tp
          assume in1:"Type (Accounts st' (Address (env::environment))) = Some (atype.Contract (Contract env)) \<and>
                     ep $$ Contract env = Some (ct', dud') \<and> ct' $$ i' = Some (Var tp)"
          have typeOld:"Type (Accounts st'' (Address env)) = Some (atype.Contract (Contract env))"
            using in1 st'Final by simp
          have stoEq:"Storage st' (Address env) = Storage st'' (Address env)"
            using st'Final by simp
          have "SCon tp i' (Storage st'' (Address env))"
            using scOld in1 typeOld unfolding safeContract_def by blast
          then show "SCon tp i' (Storage st' (Address env))"
            using stoEq by simp
        qed
      next
        show "unique_locations (Denvalue e)" using 11(2) unfolding TypeSafe_def using sameStores by simp
      next
        show "compPointers (Stack st') (Denvalue e)" using 11(2) st'Final unfolding StateInvariant_def TypeSafe_def by simp
      next
        show "balanceTypes (Accounts st')" using IH1 unfolding StateInvariant_def TypeSafe_def balanceTypes_def using st'Final sameStores by fastforce
      next
        have "envAddressesWellFormed e" using "11.prems"(1) unfolding TypeSafe_def by simp
        then show "addressFormat (Address e)" and "addressFormat (Sender e)" by simp+
      next
        show "svalueTypes (Svalue e)" using "11.prems"(1) unfolding TypeSafe_def by simp
      next
        show "lessThanTopLocs (Stack st')" using 11(2) unfolding TypeSafe_def using sameStores by simp
      next
        show "lessThanTopLocs cd" using "11.prems"(1) unfolding TypeSafe_def by simp
      next
        show "lessThanTopLocs (Memory st')" using 11(2) unfolding TypeSafe_def using sameStores by simp
      next
        show "typeCompat (Denvalue e) (Stack st') (Memory st') (Storage st' (Address e)) cd"
          unfolding typeCompat_def
        proof intros
          fix t l
          assume inDen:"(t, l) |\<in>| fmran (Denvalue e)"

          have acc:"(\<forall>adv. case Type (Accounts st adv) of None \<Rightarrow> True | Some EOA \<Rightarrow> True | Some
              (atype.Contract c) \<Rightarrow> addressFormat adv \<and> c |\<in>| fmdom ep)"
            using 11(2) unfolding TypeSafe_def AddressTypes_def by blast
          obtain cOld where cOldDef:"Type (Accounts st (Address e)) = Some (atype.Contract cOld) \<and> Contract e = cOld"
            using 11(4) unfolding fullyInitialised_def by simp
          then obtain ctO dudO where ctoDef: "ep $$ Contract e = Some (ctO, dudO)" using acc
            using "11.prems"(3) typesafe_base.fullyInitialised_def typesafe_base_axioms by blast
          have storageFinal:"Storage st' = Storage st''" using 1 by auto
          have scSt'':"safeContract (Accounts st'') (Storage st'')"
            using IH1 unfolding StateInvariant_def TypeSafe_def by blast
          have trUus:"transfer (Address e) ?newAdd v' (Accounts uus) = Some acc"
            using 1(7) uusDef by simp
          have typeStE:"Type (Accounts st (Address e)) = Some (atype.Contract (Contract e))"
            using cOldDef by simp
          have typeUusE:"Type (Accounts uus (Address e)) = Some (atype.Contract (Contract e))"
            using typeStE notSame uusDef by simp
          have typeAccE:"Type (acc (Address e)) = Some (atype.Contract (Contract e))"
            using transfer_type_same[OF trUus, of "Address e"] typeUusE by simp
          let ?stInit = "?updState\<lparr>Gas := g', Accounts := acc, Stack := k\<^sub>l, Memory := m\<^sub>l\<rparr>"
          have typeInitE:"Type (Accounts ?stInit (Address e))
                        = Some (atype.Contract (Contract e))"
            using typeAccE by simp
          have typeSt''E:"Type (Accounts st'' (Address e)) = Some (atype.Contract (Contract e))"
          proof (rule atype_same)
            show "local.stmt (snd cn) e\<^sub>l cd\<^sub>l ?stInit = Normal ((), st'')"
              using 1(8)
              using a18Exp by argo
            show "Type (Accounts ?stInit (Address e)) = Some (atype.Contract (Contract e))"
              using typeInitE .
          qed

          show "denvalueCon (Stack st') (Memory st') (Storage st' (Address e)) cd t l"
          proof(cases l)
            case (Stackloc x1)

            then show ?thesis
            proof(cases "accessStore x1 (Stack st')")
              case None
              then show ?thesis using 11(2) unfolding TypeSafe_def typeCompat_def using inDen sameStores Stackloc by fastforce
            next
              case (Some a)
              then show ?thesis
              proof(cases a)
                case (KValue x1')
                then show ?thesis using 11(2) unfolding TypeSafe_def typeCompat_def using inDen sameStores Stackloc Some by fastforce
              next
                case (KCDptr x2)
                then show ?thesis using 11(2) unfolding TypeSafe_def typeCompat_def using inDen sameStores Stackloc Some by fastforce
              next
                case (KMemptr x3)
                then show ?thesis using 11(2) unfolding TypeSafe_def typeCompat_def using inDen sameStores Stackloc Some by (cases t; fastforce)
              next
                case (KStoptr x4)
                then have accO:"accessStore x1 (Stack st) = Some( KStoptr x4)"
                  using Some 1 by auto
                then obtain struct where structDef: "t = type.Storage struct"
                  using 11(2) unfolding TypeSafe_def typeCompat_def using inDen Some KStoptr Stackloc
                  by (cases t) fastforce+
                obtain tprnt lprnt where tprntDef: "((type.Storage tprnt, Storeloc lprnt) |\<in>| fmran (Denvalue e) \<and> CompStoType tprnt struct lprnt x4)"
                  using 11(4) using accO inDen unfolding fullyInitialised_def
                  using Stackloc structDef by blast
                then have "SCon tprnt lprnt (Storage st'' (Address e))"
                proof -
                  from tprntDef have inRan: "(type.Storage tprnt, Storeloc lprnt) |\<in>| fmran (Denvalue e)" by simp
                  then obtain k where kDef: "Denvalue e $$ k = Some (type.Storage tprnt, Storeloc lprnt)"
                    using fmlookup_ran_iff by auto
                  from 11(4) obtain ct_x dud_x where
                    epX: "ep $$ (Contract e) = Some (ct_x, dud_x)" and
                    bijX: "\<forall>id v. ct_x $$ id = Some (Var v) \<longleftrightarrow> Denvalue e $$ id = Some (type.Storage v, Storeloc id)" and
                    uniqX: "\<forall>id v loc. Denvalue e $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc"
                    unfolding fullyInitialised_def by blast
                  from kDef uniqX have "k = lprnt" by auto
                  then have "Denvalue e $$ lprnt = Some (type.Storage tprnt, Storeloc lprnt)" using kDef by simp
                  then have "ct_x $$ lprnt = Some (Var tprnt)" using bijX by auto
                  moreover from epX ctoDef have "ct_x = ctO" by auto
                  ultimately have "ctO $$ lprnt = Some (Var tprnt)" by simp
                  then show ?thesis
                    using ctoDef scSt'' typeSt''E unfolding safeContract_def by blast
                qed

                then have "SCon struct x4 (Storage st'' (Address e))"
                  using tprntDef SCon_imps_sublocs by blast
                then show ?thesis using Stackloc Some KStoptr structDef storageFinal by simp
              qed
            qed
          next
            case (Storeloc x2)
            then obtain struct where structDef: "t = type.Storage struct"
              using 11(2) inDen unfolding TypeSafe_def typeCompat_def by (cases t,fastforce+)

            then have "SCon struct x2 (Storage st'' (Address e))"
            proof -
              from inDen Storeloc structDef have inRan: "(type.Storage struct, Storeloc x2) |\<in>| fmran (Denvalue e)" by simp
              then obtain k where kDef: "Denvalue e $$ k = Some (type.Storage struct, Storeloc x2)"
                using fmlookup_ran_iff by auto
              from 11(4) obtain ct_x dud_x where
                epX: "ep $$ (Contract e) = Some (ct_x, dud_x)" and
                bijX: "\<forall>id v. ct_x $$ id = Some (Var v) \<longleftrightarrow> Denvalue e $$ id = Some (type.Storage v, Storeloc id)" and
                uniqX: "\<forall>id v loc. Denvalue e $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc"
                unfolding fullyInitialised_def by blast
              from kDef uniqX have "k = x2" by auto
              then have "Denvalue e $$ x2 = Some (type.Storage struct, Storeloc x2)" using kDef by simp
              then have "ct_x $$ x2 = Some (Var struct)" using bijX by auto
              moreover from epX ctoDef have "ct_x = ctO" by auto
              ultimately have "ctO $$ x2 = Some (Var struct)" by simp
              then show ?thesis
                using ctoDef scSt'' typeSt''E unfolding safeContract_def by blast
            qed
            then show ?thesis using Storeloc structDef
              by (simp add: storageFinal)
          qed
        qed
      next
        show "denvalueTypeCorrectness e (Stack st') (Memory st')" using 1(9) 11(2) unfolding TypeSafe_def by simp
      next
        show "subPrefixStructuralConsistency (Memory st')" using 1(9) 11(2) unfolding TypeSafe_def by simp
      next
        show "SomeValSomeTyp (Memory st')" using 1(9) 11(2) unfolding TypeSafe_def by simp
      qed
    next
      have fiOld:"
        \<exists>c ct dud.
          Type (Accounts st (Address e)) = Some (atype.Contract c) \<and>
          Contract e = c \<and>
          ep $$ c = Some (ct, dud) \<and>
          (\<forall>id v. (ct $$ id = Some (Var v)) = (Denvalue e $$ id = Some (type.Storage v, Storeloc id))) \<and>
          (\<forall>id v loc. Denvalue e $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc) \<and>
          (\<forall>t l p.
              (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l (Stack st) = Some (KStoptr p) \<longrightarrow>
              (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e) \<and> CompStoType t' t l' p))"
        using 11(4) unfolding fullyInitialised_def by blast
      then obtain c_fi ct_fi dud_fi where fiC:"
          Type (Accounts st (Address e)) = Some (atype.Contract c_fi) \<and>
          Contract e = c_fi \<and>
          ep $$ c_fi = Some (ct_fi, dud_fi) \<and>
          (\<forall>id v. (ct_fi $$ id = Some (Var v)) = (Denvalue e $$ id = Some (type.Storage v, Storeloc id))) \<and>
          (\<forall>id v loc. Denvalue e $$ id = Some (type.Storage v, Storeloc loc) \<longrightarrow> id = loc)"
        and fiPtr:"\<forall>t l p.
              (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l (Stack st) = Some (KStoptr p) \<longrightarrow>
              (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e) \<and> CompStoType t' t l' p)"
        by blast
      have typeNew:"Type (Accounts st' (Address e)) = Some (atype.Contract c_fi)"
        using IH1 fiC atype_same[OF 1(8)] st'Final unfolding StateInvariant_def
        using "11.prems"(2) atype_same by presburger
      have ptrNew:"\<forall>t l p.
          (type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l (Stack st') = Some (KStoptr p) \<longrightarrow>
          (\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e) \<and> CompStoType t' t l' p)"
      proof (intro allI impI)
        fix t l p
        assume in1:"(type.Storage t, Stackloc l) |\<in>| fmran (Denvalue e) \<and> accessStore l (Stack st') = Some (KStoptr p)"
        have "accessStore l (Stack st) = Some (KStoptr p)" using in1 sameStores by simp
        then show "\<exists>t' l'. (type.Storage t', Storeloc l') |\<in>| fmran (Denvalue e) \<and> CompStoType t' t l' p"
          using fiPtr in1 by blast
      qed
      show "fullyInitialised e (Accounts st') (Stack st')"
        unfolding fullyInitialised_def using fiC typeNew ptrNew by blast

    next
      show "\<And>locs t. accessTypeStore locs (Memory st) = Some t \<Longrightarrow> accessTypeStore locs (Memory st') = Some t"
        using sameStores by auto
    next
      show "\<And>locs v.
       accessStore locs (Memory st) = Some (MPointer v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MPointer v')"
        using sameStores by auto
    next
      show "\<And>locs v. accessStore locs (Memory st) = Some (MValue v) \<Longrightarrow> \<exists>v'. accessStore locs (Memory st') = Some (MValue v')"
        using sameStores by auto
    next
      show "\<And>i loc.
       i < Toploc (Memory st) \<and> LSubPrefL2 loc (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<Longrightarrow>
       accessStore loc (Memory st) = None \<Longrightarrow> accessStore loc (Memory st') = None"
        using sameStores by auto
    next
      show "Toploc (Memory st) \<le> Toploc (Memory st')"
        using sameStores by auto
    qed
  qed
qed

end


end
