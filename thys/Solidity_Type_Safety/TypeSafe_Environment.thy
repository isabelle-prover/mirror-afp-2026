section \<open>Environment initialisation and declarations\<close>

theory TypeSafe_Environment
  imports TypeSafe_Def TypeSafe_Memory_Init TypeSafe_Memory_Copies
begin

context typesafe_base
begin

subsection \<open>Initialising an environment results in a type-safe environment\<close>
text \<open>In the call and ecall expressions all calculations are done in a clean environment.
      To do this @{const ffold_init} is used to create the environment.
      The following lemmas demonstrate the initialisation process results in a typesafe environment\<close>

subsubsection \<open>Safety of empty environments\<close>
lemma emptyTopLocs:
  shows "lessThanTopLocs emptyStore" unfolding lessThanTopLocs_def emptyStore_def accessStore_def by simp

lemma typedEmptyTopLocs:
  shows "lessThanTopLocs emptyTypedStore"
  unfolding lessThanTopLocs_def emptyStore_def emptyTypedStore_def accessStore_def by simp

lemma emptyEnvSafe:
  assumes "ev = emptyEnv addr contrct sendr sval"
    and "safeContract acc stor"
    and "balanceTypes acc"
    and "svalueTypes (Svalue ev)"
    and "lessThanTopLocs sck"
    and "lessThanTopLocs cd"
    and "lessThanTopLocs mem"
    and "addressFormat addr"
    and "addressFormat sendr"
    and "AddressTypes acc"
    and "subPrefixStructuralConsistency mem"
    and "SomeValSomeTyp mem"
  shows "TypeSafe ev acc sck mem stor cd" unfolding TypeSafe_def
proof intros
  have *:"Denvalue (ev) = fmempty" using assms(1) unfolding emptyEnv_def by simp
  then show " unique_locations (Denvalue ev)" unfolding unique_locations_def by simp
  show "AddressTypes acc" using assms by auto
  show " compPointers sck (Denvalue ev)" unfolding compPointers_def using * by (simp split:if_splits)
  show "balanceTypes acc" using assms(3) by simp
  show "svalueTypes (Svalue ev)" using assms(4) by simp
  show "lessThanTopLocs sck" using assms(5) by simp
  show " lessThanTopLocs cd" using assms(6) by simp
  show " lessThanTopLocs mem" using assms(7) by simp
  show "addressFormat (Address ev)" using assms(8) assms(1) by simp
  show "addressFormat (Sender ev)" using assms(9) assms(1) by simp
  show "safeContract acc stor" using assms by simp
  show " typeCompat (Denvalue ev) sck mem (stor (Address ev)) cd " using * unfolding typeCompat_def by simp
  show "denvalueTypeCorrectness ev sck mem" using * unfolding denvalueTypeCorrectness_def by simp
  show "subPrefixStructuralConsistency mem" using * assms unfolding subPrefixStructuralConsistency_def by simp
  show "SomeValSomeTyp mem" using assms(12) assms(1) by simp

qed


subsubsection \<open>Variable initialisation preserves unique locations\<close>
lemma envUpdate_other_unchanged:
  assumes "e' = e \<lparr>Denvalue := fmupd i ((type.Storage tp),(Storeloc i)) (Denvalue e)\<rparr>"
  shows"(\<forall>x. x \<noteq> i \<longrightarrow> fmlookup (Denvalue e') x = fmlookup (Denvalue e) x)"
proof(intros)
  fix x
  assume a1:"x \<noteq> i"
  show "Denvalue e' $$ x = Denvalue e $$ x" using assms a1 by simp
qed

text \<open>There is an assumption here that the variable being loaded does not already exist in the
environment. This is gained from the context of @{const ffold_init} as we are either loading into an empty
environment or if the location already exists then an update function is called so the value is overwritten\<close>
lemma uniqueLocationsPreserved:
  assumes "unique_locations (Denvalue e)"
  assumes "e' = e \<lparr> Denvalue := fmupd i ((type.Storage tp),(Storeloc i)) (Denvalue e) \<rparr>"
    and "(\<forall>x y. Denvalue e $$ x = Some y \<longrightarrow> snd y \<noteq> Storeloc i)"
  shows "unique_locations (Denvalue e')" unfolding unique_locations_def
proof(intros)
  fix x y
  assume a1:"x |\<in>| fmran (Denvalue e') \<and> y |\<in>| fmran (Denvalue e') \<and> snd x = snd y"
  have a2:"fmlookup (Denvalue e') i = Some ((type.Storage tp),(Storeloc i))" using assms(2) by simp
  show "x = y"
  proof(cases "Denvalue e' $$ i = Some x")
    case xt:True
    then have a3: "x = ((type.Storage tp),(Storeloc i))" using a2 by simp
    then show ?thesis
    proof(cases "Denvalue e' $$ i = Some y")
      case True
      then show ?thesis using xt by simp
    next
      case False
      then obtain t where "Some y = Denvalue e' $$ t " using assms a1 fmranE by metis
      then have "Denvalue e $$ t = Some y" using assms a1 False by auto
      then have "snd y \<noteq> snd x" using assms a1 a3 by fastforce
      then show ?thesis using a1 assms by simp
    qed
  next
    case xf:False
    then show ?thesis
    proof(cases "Denvalue e' $$ i = Some y")
      case True
      then obtain t where "Some x = Denvalue e' $$ t " using assms a1 fmranE by metis
      then have "Denvalue e $$ t = Some x" using assms a1 xf by auto
      then have "snd y \<noteq> snd x" using assms True a1 a2 xf by fastforce
      then show ?thesis using a1 by simp
    next
      case False
      then show ?thesis using False a1 assms envUpdate_other_unchanged fmranE fmranI unique_locations_def xf by metis
    qed
  qed
qed


lemma compPointersPreserved:
  assumes "compPointers st (Denvalue e)"
  assumes "e' = e \<lparr> Denvalue := fmupd i ((type.Storage tp), (Storeloc i)) (Denvalue e) \<rparr>"
    and "SCon tp i (stor (Address e'))"
    and "TypeSafe e acc st mem stor cd"
    and "(\<forall>x y. Denvalue e $$ x = Some y \<longrightarrow> snd y \<noteq> Storeloc i)"
    and "\<forall>x y. Denvalue e $$ x = Some y \<longrightarrow> snd y = Storeloc x"
    and "\<forall> x y t1 t2. x \<noteq> y \<and> Denvalue e $$ x = Some (type.Storage t1, Storeloc x) \<and> Denvalue e $$ y = Some (type.Storage t2, Storeloc y)
        \<longrightarrow> \<not>TypedStoSubpref x y t2 \<and> \<not>TypedStoSubpref y x t1"
    and "\<forall>x t1. x \<noteq> i \<and> Denvalue e $$ x = Some (type.Storage t1, Storeloc x) \<longrightarrow> \<not>TypedStoSubpref x i tp \<and> \<not>TypedStoSubpref i x t1"
  shows "compPointers st (Denvalue e')"
  unfolding compPointers_def
proof (intro allI impI)
  fix tp1 tp2 l1 l2 l1' l2' stl1 stl2
  have a2:"fmlookup (Denvalue e') i = Some ((type.Storage tp),(Storeloc i))" using assms(2) by simp
  have storSame:"stor (Address e') = stor (Address e)" using assms(2) by simp
  assume *: "(type.Storage tp1, l1) |\<in>| fmran (Denvalue e') \<and>
       (type.Storage tp2, l2) |\<in>| fmran (Denvalue e') \<and>
       (l1 = Stackloc l1' \<and> accessStore l1' st = Some (KStoptr stl1) \<or> l1 = Storeloc stl1) \<and> (l2 = Stackloc l2' \<and> accessStore l2' st = Some (KStoptr stl2) \<or> l2 = Storeloc stl2)"
  show "if TypedStoSubpref stl2 stl1 tp1 then CompStoType tp1 tp2 stl1 stl2
        else if TypedStoSubpref stl1 stl2 tp2 then CompStoType tp2 tp1 stl2 stl1 else True"

  proof(cases "TypedStoSubpref stl2 stl1 tp1")
    case **:True
    have "CompStoType tp1 tp2 stl1 stl2"
    proof(cases "Denvalue e' $$ i = Some (type.Storage tp1, l1)")
      case t1:True
      then have a3: "(type.Storage tp1, l1) = ((type.Storage tp),(Storeloc i))" using assms(2) by simp
      then show ?thesis
      proof(cases "Denvalue e' $$ i = Some (type.Storage tp2, l2)")
        case True
        then have a4:"(type.Storage tp1, l1) = (type.Storage tp2, l2)" using assms(2) a3 by simp
        then have "tp1 = tp \<and> tp2 = tp" using a3 by simp
        moreover have "l1 = Storeloc i \<and> l2 = Storeloc i" using a3 a4 by simp
        ultimately show ?thesis using assms(3) * CompStoType.simps **
          by (metis denvalue.distinct(1) denvalue.inject(2) stypes.exhaust)
      next
        case False
        then have a5:"(type.Storage tp2, l2) |\<in>| fmran (Denvalue e)" using assms(1) unfolding compPointers_def using * assms envUpdate_other_unchanged fmranE fmranI by metis
        then have a10:"l2 \<noteq> Storeloc i" using * ** t1 assms(5) fmranE by auto
        then have a20:"l1 = Storeloc i" using a3 by simp
        then have a30:"tp = tp1" using a3 by simp
        then have a40:"stl1 = i" using * a20 by simp
        have "\<forall>c. l2 \<noteq> Stackloc c" using assms(6) a5 by fastforce
        then obtain i' where i'Def: "l2 = Storeloc i' \<and> i' \<noteq> i \<and> stl2 = i'" using a10 * by auto
        show ?thesis using ** assms(7) assms(8)
          by (metis denvalue.inject(2) i'Def a30 a40 a5 assms(6) fmranE snd_conv)
      qed
    next
      case f2:False
      then have a5:"(type.Storage tp1, l1) |\<in>| fmran (Denvalue e)" using assms(1) unfolding compPointers_def using * assms envUpdate_other_unchanged fmranE fmranI by metis
      then show ?thesis
      proof(cases "Denvalue e' $$ i = Some (type.Storage tp2, l2)")
        case True
        then have a3: "(type.Storage tp2, l2) = ((type.Storage tp),(Storeloc i))" using assms(2) by simp
        then have a20:"l1 \<noteq> Storeloc i" using a3 a5 * ** assms(5) fmranE by auto
        then have a30:"tp = tp2" using a3 by simp
        then have a40:"stl2 = i" using * a20 using a3 by auto
        have "\<forall>c. l2 \<noteq> Stackloc c" using assms(6) a5 a3 by auto
        then obtain i' where a50:"l2 = Storeloc i' \<and> i' \<noteq> i \<and> stl2 = i'" using *
          by (metis "**" denvalue.distinct(1) denvalue.inject(2) a20 a5 assms(6) assms(8) fmranE sndI)
        show ?thesis using ** assms(7) assms(8)
          using a50 a40 by fastforce
      next
        case False
        then have a6:"(type.Storage tp2, l2) |\<in>| fmran (Denvalue e)" using assms(1) unfolding compPointers_def using * assms envUpdate_other_unchanged fmranE fmranI by metis
        then obtain x where b10:"Denvalue e $$ x = Some (type.Storage tp2, Storeloc x)" using fmranE assms(5) by (metis assms(6) snd_conv)
        then obtain y where b20:"Denvalue e $$ y = Some (type.Storage tp1, Storeloc y)" using a5 fmranE assms(5) by (metis assms(6) snd_conv)
        then show ?thesis using ** assms(4) a6 a5 b10 b20 fmranE unfolding TypeSafe_def compPointers_def using "*" by force
      qed
    qed
    then show ?thesis by (simp add: "**")
  next
    case f2:False
    then show ?thesis
    proof(cases "TypedStoSubpref stl1 stl2 tp2")
      case **:True
      have "CompStoType tp2 tp1 stl2 stl1"
      proof(cases "Denvalue e' $$ i = Some (type.Storage tp1, l1)")
        case t1:True
        then have a3: "(type.Storage tp1, l1) = ((type.Storage tp),(Storeloc i))" using assms(2) by simp
        then show ?thesis
        proof(cases "Denvalue e' $$ i = Some (type.Storage tp2, l2)")
          case True
          then have a4:"(type.Storage tp1, l1) = (type.Storage tp2, l2)" using assms(2) a3 by simp
          then have "tp1 = tp \<and> tp2 = tp" using a3 by simp
          moreover have "l1 = Storeloc i \<and> l2 = Storeloc i" using a3 a4 by simp
          ultimately show ?thesis using assms(3) *
            using "**" f2 by auto
        next
          case False
          then have a5:"(type.Storage tp2, l2) |\<in>| fmran (Denvalue e)"
            using assms(1) unfolding compPointers_def using * assms envUpdate_other_unchanged fmranE fmranI by metis
          then have a10:"l2 \<noteq> Storeloc i" using * ** t1 assms(5) fmranE by auto
          then have a20:"l1 = Storeloc i" using a3 by simp
          then have a30:"tp = tp1" using a3 by simp
          then have a40:"stl1 = i" using * a20 by simp
          have "\<forall>c. l2 \<noteq> Stackloc c" using assms(6) a5 by fastforce
          then obtain i' where i'Def: "l2 = Storeloc i' \<and> i' \<noteq> i \<and> stl2 = i'" using a10 * by auto
          show ?thesis using ** assms(7) assms(8)
            by (metis denvalue.inject(2) i'Def a40 a5 assms(6) fmranE snd_conv)
        qed
      next
        case f3:False
        then have a5:"(type.Storage tp1, l1) |\<in>| fmran (Denvalue e)" using assms(1) unfolding compPointers_def using * assms envUpdate_other_unchanged fmranE fmranI by metis
        then show ?thesis
        proof(cases "Denvalue e' $$ i = Some (type.Storage tp2, l2)")
          case True
          then have a3: "(type.Storage tp2, l2) = ((type.Storage tp),(Storeloc i))" using assms(2) by simp
          then have a20:"l1 \<noteq> Storeloc i" using a3 a5 * ** assms(5) fmranE by auto
          then have a30:"tp = tp2" using a3 by simp
          then have a40:"stl2 = i" using * a20 using a3 by auto
          have "\<forall>c. l1 \<noteq> Stackloc c" using assms(6) a5 by fastforce
          then obtain i' where a50:"l1 = Storeloc i' \<and> i' \<noteq> i \<and> stl1= i'" using * a40 a20
            by simp
          show ?thesis using ** assms(7) assms(8)
            using a50 a40 by (metis denvalue.inject(2) a30 a5 assms(6) fmranE snd_conv)
        next
          case False
          then have a6:"(type.Storage tp2, l2) |\<in>| fmran (Denvalue e)" using assms(1) unfolding compPointers_def using * assms envUpdate_other_unchanged fmranE fmranI by metis
          then obtain x where b10:"Denvalue e $$ x = Some (type.Storage tp2, Storeloc x)" using fmranE assms(5) by (metis assms(6) snd_conv)
          then obtain y where b20:"Denvalue e $$ y = Some (type.Storage tp1, Storeloc y)" using a5 fmranE assms(5) by (metis assms(6) snd_conv)
          then show ?thesis using ** f2 f3 assms(4) a6 a5 b10 b20 fmranE unfolding TypeSafe_def compPointers_def using "*" by force
        qed
      qed
      then show ?thesis by (simp add: "**" f2 )
    next
      case False
      then show ?thesis using f2 by simp
    qed
  qed
qed

lemma compPointersNonStackUpd:
  assumes "compPointers sck' (Denvalue ev')"
    and "Denvalue e = Denvalue (ev'\<lparr>Denvalue := Denvalue ev'(ip $$:= (t, (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')))))\<rparr>)"
    and "\<forall>t'. t \<noteq> type.Storage t'"
    and "k' = push v sck'"
    and "lessThanTopLocs sck'"
    and "TypeSafe ev' (Accounts st) sck' mem' (Storage st) cd'"
    and "Address ev' = Address e"
  shows "compPointers k' (Denvalue e)" unfolding compPointers_def
proof intros
  fix tp1 tp2 l1 l2 l1' l2' stl1 stl2
  assume *:" (type.Storage tp1, l1) |\<in>| fmran (Denvalue e) \<and>
       (type.Storage tp2, l2) |\<in>| fmran (Denvalue e) \<and>
       (l1 = Stackloc l1' \<and> accessStore l1' k' = Some (KStoptr stl1) \<or> l1 = Storeloc stl1) \<and> (l2 = Stackloc l2' \<and> accessStore l2' k' = Some (KStoptr stl2) \<or> l2 = Storeloc stl2)"
  have b5: "fmlookup (Denvalue e) ip = Some (t,(Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))))" using assms by simp
  have b6:"\<forall>i''. i'' \<noteq> ip \<longrightarrow> fmlookup (Denvalue e) i'' = fmlookup (Denvalue ev') i''" using assms fmupd_def by fastforce
  have b7:"\<forall>loc''. loc'' \<noteq> (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')) \<longrightarrow> accessStore loc'' k' = accessStore loc'' sck'"
    using assms unfolding push_def allocate_def accessStore_def updateStore_def by simp
  have b8:"\<forall>x y. Denvalue ev' $$ x = Some y \<longrightarrow> snd y \<noteq> Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))"
    using stackLocs_imp_NotDen[of sck' ev' st mem'] assms by auto
  then have b15:"fmlookup (Denvalue e) ip \<noteq> Some (type.Storage tp1, l1) \<and> fmlookup (Denvalue e) ip \<noteq> Some (type.Storage tp2, l2)" using b5 assms by simp
  then have b20:"(type.Storage tp1, l1) |\<in>| fmran (Denvalue ev') \<and> (type.Storage tp2, l2) |\<in>| fmran (Denvalue ev')"
    using b6 * by (metis fmlookup_ran_iff)
  then have b25:"l1 \<noteq>(Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck'))) \<and> l2 \<noteq> (Stackloc (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc sck')))"
    using b5 * b8 b20 by fastforce
  then show "if TypedStoSubpref stl2 stl1 tp1 then CompStoType tp1 tp2 stl1 stl2 else if TypedStoSubpref stl1 stl2 tp2 then CompStoType tp2 tp1 stl2 stl1 else True"
  proof(cases "stl1 = stl2")
    case True
    then show ?thesis
    proof(cases "l1")
      case st1:(Stackloc x1)
      then have a1:"accessStore x1 sck' = Some (KStoptr stl1)" using assms(6) unfolding TypeSafe_def compPointers_def using b20 "*" b25 b7 by auto
      then show ?thesis
      proof(cases "l2")
        case (Stackloc x2)
        then have "accessStore x2 sck' = Some (KStoptr stl2)" using assms(6) unfolding TypeSafe_def compPointers_def using b20 "*" b25 b7 by auto
        then show ?thesis using True assms(6) a1 st1 Stackloc unfolding TypeSafe_def compPointers_def using b20 by blast
      next
        case (Storeloc x2)
        then show ?thesis using True assms(6) a1 st1 unfolding TypeSafe_def compPointers_def using b20 using "*" by blast
      qed
    next
      case str1:(Storeloc x2)
      then have a1:"stl1 = x2" using * by simp
      then show ?thesis
      proof(cases "l2")
        case (Stackloc x2)
        then have "accessStore x2 sck' = Some (KStoptr stl2)" using assms(6) unfolding TypeSafe_def compPointers_def using b20 "*" b25 b7 by auto
        then show ?thesis using True assms(6) a1 str1 Stackloc unfolding TypeSafe_def compPointers_def using b20 by blast
      next
        case (Storeloc x2)
        then show ?thesis using True assms(6) a1 str1 unfolding TypeSafe_def compPointers_def using b20 using "*" by blast
      qed
    qed
  next
    case f1:False
    then show ?thesis
    proof(cases "TypedStoSubpref stl2 stl1 tp1")
      case t2:True
      then show ?thesis
      proof(cases "l1")
        case st1:(Stackloc x1)
        then have a1:"accessStore x1 sck' = Some (KStoptr stl1)" using assms(6) unfolding TypeSafe_def compPointers_def using b20 "*" b25 b7 by auto
        then show ?thesis
        proof(cases "l2")
          case (Stackloc x2)
          then have "accessStore x2 sck' = Some (KStoptr stl2)" using assms(6) unfolding TypeSafe_def compPointers_def using b20 "*" b25 b7 by auto
          then show ?thesis using f1 t2 assms(6) a1 st1 Stackloc unfolding TypeSafe_def compPointers_def using b20 by blast
        next
          case (Storeloc x2)
          then show ?thesis using f1 t2 assms(6) a1 st1 unfolding TypeSafe_def compPointers_def using b20 using "*" by blast
        qed
      next
        case str1:(Storeloc x2)
        then have a1:"stl1 = x2" using * by simp
        then show ?thesis
        proof(cases "l2")
          case (Stackloc x2)
          then have "accessStore x2 sck' = Some (KStoptr stl2)" using assms(6) unfolding TypeSafe_def compPointers_def using b20 "*" b25 b7 by auto
          then show ?thesis using f1 t2 assms(6) a1 str1 Stackloc unfolding TypeSafe_def compPointers_def using b20 by blast
        next
          case (Storeloc x2)
          then show ?thesis using f1 t2 assms(6) a1 str1 unfolding TypeSafe_def compPointers_def using b20 using "*" by blast
        qed
      qed
    next
      case f2:False
      then show ?thesis
      proof(cases " TypedStoSubpref stl1 stl2 tp2 ")
        case t3:True
        then show ?thesis
        proof(cases "l1")
          case st1:(Stackloc x1)
          then have a1:"accessStore x1 sck' = Some (KStoptr stl1)" using assms(6) unfolding TypeSafe_def compPointers_def using b20 "*" b25 b7 by auto
          then show ?thesis
          proof(cases "l2")
            case (Stackloc x2)
            then have "accessStore x2 sck' = Some (KStoptr stl2)" using assms(6) unfolding TypeSafe_def compPointers_def using b20 "*" b25 b7 by auto
            then show ?thesis using f1 f2 assms(6) a1 st1 Stackloc unfolding TypeSafe_def compPointers_def using b20 by blast
          next
            case (Storeloc x2)
            then show ?thesis using f1 f2 assms(6) a1 st1 unfolding TypeSafe_def compPointers_def using b20 using "*" by blast
          qed
        next
          case str1:(Storeloc x2)
          then have a1:"stl1 = x2" using * by simp
          then show ?thesis
          proof(cases "l2")
            case (Stackloc x2)
            then have "accessStore x2 sck' = Some (KStoptr stl2)" using assms(6) unfolding TypeSafe_def compPointers_def using b20 "*" b25 b7 by auto
            then show ?thesis using assms(6) a1 str1 Stackloc unfolding TypeSafe_def compPointers_def using b20 by blast
          next
            case (Storeloc x2)
            then show ?thesis using assms(6) a1 str1 unfolding TypeSafe_def compPointers_def using b20 using "*" by blast
          qed
        qed
      next
        case t4:False
        then show ?thesis using f1 f2 by simp
      qed
    qed
  qed
qed


lemma ffoldInitAllLocsStorage:
  shows "\<forall>e' x y. ffold (init ct) (emptyEnv (Address e2) (Contract e) (Sender e3) sval) xs = e'
          \<longrightarrow> ( (Denvalue e') $$ x = Some y \<longrightarrow> (snd y) = Storeloc x )

              "
proof(induct xs)
  case empty
  then show ?case
  proof(intros)
    fix e' x y
    assume **:"ffold (init ct) (emptyEnv (Address e2) (Contract e) (Sender e3) sval) {||} = e'"
    then have ***:"e' = emptyEnv(Address e2) (Contract e) (Sender e3) sval" using FSet.comp_fun_commute.ffold_empty[OF init_commte] by simp

    assume ****:"Denvalue e' $$ x = Some y "
    have "Denvalue e' = fmempty" using *** by simp
    then have a23:"(Denvalue e') $$ x = None" by simp
    then show "snd y = Storeloc x" using ** **** by simp
  qed
next
  case (insert x xs)
  then have *: "ffold (init ct) (emptyEnv (Address e2) (Contract e) (Sender e3) sval) (finsert x xs) =
    init ct x (ffold (init ct) (emptyEnv (Address e2) (Contract e) (Sender e3) sval) xs)" using FSet.comp_fun_commute.ffold_finsert[OF init_commte] by simp
  show ?case
  proof (intros)
    fix e' xa y ya assume **: "ffold (init ct) (emptyEnv (Address e2) (Contract e) (Sender e3) sval) (finsert x xs) = e'"
    obtain e'' where ***: "ffold (init ct) (emptyEnv (Address e2) (Contract e) (Sender e3) sval) xs = e''" using * by simp
    then have a15: "(Denvalue e'' $$ x = Some y \<longrightarrow> snd y = Storeloc x)" using insert * *** by blast
    then have a20:"init ct x e'' = e'" using * ** *** by simp
    then have a23:"Contract e = Contract (emptyEnv (Address e) (Contract e) (Sender e) (Svalue e))" using a20 by simp
    then have a25: "Contract e = Contract e''" using *** ffold_init_contract by auto
    have "(case ct $$ x of None \<Rightarrow> e'' | Some (Var tp) \<Rightarrow> updateEnvDup x (type.Storage tp) (Storeloc x) e'' | Some _ \<Rightarrow> e'') = e'"
      using init_def[of ct x e''] a20 by auto


    assume a40:"Denvalue e' $$ xa = Some y"
    show "snd y = Storeloc xa"
    proof (cases "Denvalue e'' $$ xa = Some y")
      case True
      then show ?thesis using insert *** by blast
    next
      case False
      then have a50:"Denvalue e' \<noteq> Denvalue e''" using a40 by auto
      then obtain tp where a60:"fmlookup ct x = Some (Var tp)" using a50 a20 a40 init_def by (simp split:option.splits member.splits )
      then have a70:"Denvalue e' = Denvalue(updateEnvDup x (type.Storage tp) (Storeloc x) e'')" using a50 a20 a40 by (simp split:option.splits member.splits )
      then have a80:"Denvalue e' = Denvalue(e''\<lparr> Denvalue := fmupd x ((type.Storage tp),(Storeloc x)) (Denvalue e'')\<rparr>)" using
          updateEnvDup.simps updateEnv.simps by (metis a20 a50 a60 init_s12 init_s13)
      then have a90:"xa = x" using a70 a40 a20 a50 a60 init_def updateEnvDup_dup False by metis
      then have "Denvalue e' $$ x = Some ((type.Storage tp),(Storeloc x))" using a80 by simp
      then have "y = ((type.Storage tp), (Storeloc x))" using a90 a40 by simp
      then show ?thesis using a90 by simp
    qed

  qed
qed

lemma DenvalueChange:
  assumes "e' = e\<lparr>Denvalue := Denvalue e(i $$:= y)\<rparr>"
    and "z \<noteq> i"
  shows "Denvalue e' $$ z = Denvalue e $$ z" using assms fmranI fmranE by auto


subsubsection \<open>Initialising a single variable preserves type safety\<close>
lemma initEmptySafe:
  assumes "TypeSafe e acc st mem stor cd"
  assumes "init ct i e = e'"
    and "ep $$ Contract (e::environment) = Some(ct, dud)"
    and "Type (acc (Address (e::environment))) = Some (atype.Contract (Contract e))"
    and "\<forall>x y. (Denvalue e) $$ x = Some y \<longrightarrow> (snd y) = Storeloc x"
    and "\<forall>l y. \<exists>t1. (Denvalue e) $$ l = Some y \<longrightarrow> ct $$ l = Some (Var t1) \<and> (fst y) = type.Storage t1"
  shows "TypeSafe e' acc st mem stor cd"
proof (cases "fmlookup ct i")
  case None
  then have "init ct i e = e" using init_def by simp
  then show ?thesis using assms by simp
next
  case (Some a)
  then show ?thesis
  proof(cases a)
    case (Method x1)
    then have "init ct i e = e" using init_def Some by simp
    then show ?thesis using assms by simp
  next
    case (Function x2)
    then show ?thesis using init_def Some assms by simp
  next
    case (Var tp)
    then have a0:"ct $$ i = Some (Var tp)" using Some by auto
    have a1:"\<forall>c adv ct dud i1 i2 t1 t2.
     i1 \<noteq> i2 \<and> ep $$ c = Some (ct, dud) \<and> ct $$ i1 = Some (Var t1) \<and> ct $$ i2 = Some (Var t2) \<longrightarrow>
     \<not> TypedStoSubpref i1 i2 t2 \<and> \<not> TypedStoSubpref i2 i1 t1"
      using methodVarsNoPref by blast
    have a5:"Address e = Address e'" using init_def Some assms(2) Var by (auto split:option.split)
    have a51:"Contract e = Contract e'"using init_def Some assms(2) Var by (auto split:option.split)
    then have "init ct i e = updateEnvDup i (type.Storage tp) (Storeloc i) e" using Var init_def Some by simp
    then have e'Def:"e' = (case fmlookup (Denvalue e) i of
              Some _ \<Rightarrow> e
            | None \<Rightarrow> updateEnv i (type.Storage tp) (Storeloc i) e)" using updateEnvDup.simps assms(2) by simp
    then show ?thesis
    proof (cases "fmlookup (Denvalue e) i")
      case None
      then have a6:"e' = updateEnv i (type.Storage tp) (Storeloc i) e" using updateEnvDup.simps assms(2) Some Var by simp
      then have a10:"e' = e \<lparr> Denvalue := fmupd i ((type.Storage tp),(Storeloc i)) (Denvalue e) \<rparr>" using updateEnv.simps by simp

      have a14:"Type (acc (Address (e'::environment))) = Some (atype.Contract (Contract e'))"
        using assms(4) a5 a51 by simp

      have a15:" (\<forall>e ct dud i tp.
      Type (acc (Address (e::environment))) = Some (atype.Contract (Contract e)) \<and>
      ep $$ Contract e = Some (ct, dud) \<and> ct $$ i = Some (Var tp) \<longrightarrow>
      SCon tp i (stor (Address (e::environment))))"
        using assms(1) unfolding TypeSafe_def safeContract_def by blast

      then have a20:"SCon tp i (stor (Address e'))" using a15 a0 a14 assms(3)
        by (metis a0 a14 a51)

      show ?thesis unfolding TypeSafe_def
      proof(intros)
        show "safeContract acc stor" using assms(1) TypeSafe_def by simp
        show "balanceTypes acc" using assms TypeSafe_def by simp

      next
        have a30:"svalueTypes (Svalue e)" using assms TypeSafe_def by simp
        then have "Svalue e= Svalue e'" using a10 by simp
        show "svalueTypes (Svalue e')" using assms TypeSafe_def svalueTypes_def a30 a10 by simp
      next
        show "typeCompat (Denvalue e') st mem (stor (Address e')) cd" unfolding typeCompat_def
        proof intros
          fix t l
          assume a40:"(t, l) |\<in>| fmran (Denvalue e')"
          then obtain x where a50:"fmlookup (Denvalue e') x = Some(t,l)" by auto
          show "denvalueCon st mem (stor (Address e')) cd t l"
          proof(cases "x = i")
            case True
            then have a60:"fmlookup (Denvalue e') x = Some ((type.Storage tp),(Storeloc i))" using a10 a50 by simp
            moreover have "l = Storeloc i" using a50 a60 by simp
            moreover have "t = type.Storage tp" using a50 a60 by simp
            ultimately show ?thesis using a20 by simp
          next
            case False
            then have a60:"fmlookup (Denvalue e) x = fmlookup (Denvalue e') x" using envUpdate_other_unchanged a10 by simp
            then have a70:"(t, l) |\<in>| fmran (Denvalue e)" using False a40 a50 by (simp add: fmranI)
            then show ?thesis using assms(1) unfolding TypeSafe_def typeCompat_def using a70 a5 a60 by metis
          qed
        qed
      next
        have *:"unique_locations (Denvalue e)" using assms TypeSafe_def by simp
        have **:"(\<forall>x y. Denvalue e $$ x = Some y \<longrightarrow> snd y \<noteq> Storeloc i)" using None assms by fastforce
        show "unique_locations (Denvalue e')" using uniqueLocationsPreserved * ** a10 by blast
      next
        have *:"compPointers st (Denvalue e)" using assms TypeSafe_def by simp
        have **:"(\<forall>x y. Denvalue e $$ x = Some y \<longrightarrow> snd y \<noteq> Storeloc i)" using None assms by fastforce
        have a21:"SCon tp i (stor (Address e'))" using a20 by simp
        have "init ct i e = e'" using assms by simp
        moreover have "\<forall>x y t1 t2. x \<noteq> y \<and> Denvalue e $$ x = Some (type.Storage t1, Storeloc x)
              \<and> Denvalue e $$ y = Some (type.Storage t2, Storeloc y)
              \<longrightarrow> \<not> TypedStoSubpref x y t2 \<and> \<not> TypedStoSubpref y x t1"
        proof intros
          fix x y t1 t2
          assume b99:"x \<noteq> y \<and> Denvalue e $$ x = Some (type.Storage t1, Storeloc x) \<and> Denvalue e $$ y = Some (type.Storage t2, Storeloc y)"
          then have b98:"ct $$ x = Some (Var t1)" using assms(6) by auto
          moreover have b97:"ct $$ y = Some (Var t2)" using assms(6) b99 by auto
          ultimately show " \<not> TypedStoSubpref x y t2" using a1 assms(3) b99 by metis
          show "\<not> TypedStoSubpref y x t1" using a1 assms(3) b99 b98 b97 by metis
        qed

        moreover have "\<forall>x t1. x \<noteq> i \<and> Denvalue e $$ x = Some (type.Storage t1, Storeloc x) \<longrightarrow> \<not> TypedStoSubpref x i tp \<and> \<not> TypedStoSubpref i x t1"
          using assms(5) assms(6) assms(3) assms(1) a1 a0 unfolding TypeSafe_def
          by (metis type.inject(4) fst_conv)
        ultimately show "compPointers st (Denvalue e')" using a6 a10 compPointersPreserved[of st e e' i tp] assms(1) a21 * ** assms(5) by blast
      next
        show "lessThanTopLocs st" using assms TypeSafe_def by simp
      next
        show "lessThanTopLocs cd" using assms TypeSafe_def by simp
      next
        show "lessThanTopLocs mem" using assms TypeSafe_def by simp
      next
        show "addressFormat (Address e')" using assms unfolding TypeSafe_def by auto
      next
        show "addressFormat (Sender e')" using assms unfolding TypeSafe_def by auto
      next
        show "AddressTypes acc" using assms unfolding TypeSafe_def by blast
      next
        have "(\<forall>x y i''. Denvalue e' $$ x = Some y \<longrightarrow> snd y \<noteq> Stackloc i'')" using assms a10 by auto
        then show "denvalueTypeCorrectness e' st mem"
          using assms unfolding TypeSafe_def denvalueTypeCorrectness_def by fastforce
      next
        show "subPrefixStructuralConsistency mem"
          using assms unfolding TypeSafe_def subPrefixStructuralConsistency_def by fastforce
      next
        show "SomeValSomeTyp mem" using assms unfolding TypeSafe_def by blast
      qed
    next
      case some2:(Some a)
      then have a6:"e' = e" using updateEnvDup.simps assms(2) Some Var by simp
      then show ?thesis using assms by simp
    qed
  qed
qed

subsubsection \<open>Initialising multiple variables from an empty environment is type-safe\<close>
lemma ffoldInitTypeSafe:
  assumes " safeContract acc stor"
    and "balanceTypes acc"
    and "svalueTypes sval"
    and "lessThanTopLocs mem"
    and "ep $$ Contract e = Some(ct, dud)"
    and "addressFormat (e2)"
    and "addressFormat (e3)"
    and "AddressTypes acc"
    and "subPrefixStructuralConsistency mem"
    and "SomeValSomeTyp mem"
    and "Type (acc e2) = Some (atype.Contract (Contract e))"
  shows "\<forall>e' x y. ffold (init ct) (emptyEnv (e2) (Contract e) (e3) sval) xs = e'
          \<longrightarrow> TypeSafe e' acc emptyStore mem stor emptyTypedStore
              \<and>( (Denvalue e') $$ x = Some y \<longrightarrow> (snd y) = Storeloc x )
              \<and> ( Denvalue e' $$ x = Some y \<longrightarrow> (\<exists>t1. ct $$ x = Some (Var t1) \<and> fst y = type.Storage t1))
              "
proof(induct xs)
  case empty
  then show ?case
  proof(intros)
    fix e' x y
    assume **:"ffold (init ct) (emptyEnv (e2) (Contract e) ( e3) sval) {||} = e'"
    then have ***:"e' = emptyEnv(e2) (Contract e) ( e3) sval" using FSet.comp_fun_commute.ffold_empty[OF init_commte] by simp
    then have "svalueTypes sval" unfolding emptyEnv_def using assms(3) svalueTypes_def by simp
    have " safeContract acc stor" using assms(1) ***
      using safeContract_def by force
    then show "TypeSafe e' acc emptyStore mem stor emptyTypedStore"
      using ** *** assms emptyEnvSafe emptyTopLocs typedEmptyTopLocs emptyEnv_svalue
      by (metis)
    assume a22: "Denvalue e' $$ x = Some y"
    have "Denvalue e' = fmempty" using *** by simp
    then have a23:"(Denvalue e') $$ x = None" by simp
    then show "snd y = Storeloc x" using a22 by simp
    then show " \<exists>t1. ct $$ x = Some (Var t1) \<and> fst y = type.Storage t1" using a22 a23 by auto
  qed
next
  case (insert x xs)
  then have *: "ffold (init ct) (emptyEnv (e2) (Contract e) ( e3) sval) (finsert x xs) =
    init ct x (ffold (init ct) (emptyEnv (e2) (Contract e) ( e3) sval) xs)" using FSet.comp_fun_commute.ffold_finsert[OF init_commte] by simp
  show ?case
  proof (intros)
    fix e' xa y ya assume **: "ffold (init ct) (emptyEnv ( e2) (Contract e) ( e3) sval) (finsert x xs) = e'"
    obtain e'' where ***: "ffold (init ct) (emptyEnv ( e2) (Contract e) ( e3) sval) xs = e''" using * by simp
    then have a10:"TypeSafe e'' acc emptyStore mem stor emptyTypedStore" using insert * by simp
    then have a15: "(Denvalue e'' $$ x = Some y \<longrightarrow> snd y = Storeloc x)" using insert * *** by blast
    then have a16:" Denvalue e'' $$ xa = Some ya \<longrightarrow> (\<exists>t1. ct $$ xa = Some (Var t1) \<and> fst ya = type.Storage t1)" using insert * *** a10 by blast
    then have a20:"init ct x e'' = e'" using * ** *** by simp
    then have a23:"Contract e = Contract (emptyEnv (Address e) (Contract e) (Sender e) (Svalue e))" using a20 by simp
    then have a25: "Contract e = Contract e''" using *** ffold_init_contract by auto
    have a26: "Address e'' = e2" using *** ffold_init_ad_same
      by force
    have a27: "Type (acc (Address e'')) = Some (atype.Contract (Contract e''))"
      using assms(11) a25 a26 by simp
    have "(case ct $$ x of None \<Rightarrow> e'' | Some (Var tp) \<Rightarrow> updateEnvDup x (type.Storage tp) (Storeloc x) e'' | Some _ \<Rightarrow> e'') = e'"
      using init_def[of ct x e''] a20 by auto
    then show a30:"TypeSafe e' acc emptyStore mem stor emptyTypedStore"
      using initEmptySafe[of e'' acc emptyStore mem stor emptyTypedStore ct x] assms(2)
            a10 a15 a20 a25 a16 insert *** assms(5) a27 by metis

    assume a40:"Denvalue e' $$ xa = Some y"
    show "snd y = Storeloc xa"
    proof (cases "Denvalue e'' $$ xa = Some y")
      case True
      then show ?thesis using insert *** by blast
    next
      case False
      then have a50:"Denvalue e' \<noteq> Denvalue e''" using a40 by auto
      then obtain tp where a60:"fmlookup ct x = Some (Var tp)" using a50 a20 a40 init_def by (simp split:option.splits member.splits )
      then have a70:"Denvalue e' = Denvalue(updateEnvDup x (type.Storage tp) (Storeloc x) e'')" using a50 a20 a40 by (simp split:option.splits member.splits )
      then have a80:"Denvalue e' = Denvalue(e''\<lparr> Denvalue := fmupd x ((type.Storage tp),(Storeloc x)) (Denvalue e'')\<rparr>)" using
          updateEnvDup.simps updateEnv.simps by (metis a20 a50 a60 init_s12 init_s13)
      then have a90:"xa = x" using a70 a40 a20 a50 a60 init_def updateEnvDup_dup False by metis
      then have "Denvalue e' $$ x = Some ((type.Storage tp),(Storeloc x))" using a80 by simp
      then have "y = ((type.Storage tp), (Storeloc x))" using a90 a40 by simp
      then show ?thesis using a90 by simp
    qed
    show "\<exists>t1. ct $$ xa = Some (Var t1) \<and> fst y = type.Storage t1"
    proof (cases "Denvalue e'' $$ xa = Some y")
      case True
      then show ?thesis using insert *** by blast
    next
      case False
      then have a50:"Denvalue e' \<noteq> Denvalue e''" using a40 by auto
      then obtain tp where a60:"fmlookup ct x = Some (Var tp)" using a50 a20 a40 init_def by (simp split:option.splits member.splits )
      then have a70:"Denvalue e' = Denvalue(updateEnvDup x (type.Storage tp) (Storeloc x) e'')" using a50 a20 a40 by (simp split:option.splits member.splits )
      then have a80:"Denvalue e' = Denvalue(e''\<lparr> Denvalue := fmupd x ((type.Storage tp),(Storeloc x)) (Denvalue e'')\<rparr>)" using
          updateEnvDup.simps updateEnv.simps by (metis a20 a50 a60 init_s12 init_s13)
      then have a90:"xa = x" using a70 a40 a20 a50 a60 init_def updateEnvDup_dup False by metis
      then have "Denvalue e' $$ x = Some ((type.Storage tp),(Storeloc x))" using a80 by simp
      then show ?thesis using a90 a60 a80 a60 a40 by auto
    qed
  qed
qed

lemma ffoldInit_var_storage_mapping:
  assumes "ffold (init ct) (emptyEnv adv c adde v') (fmdom ct) = loaded"
  shows "\<forall>id v. ct $$ id = Some (Var v) \<longrightarrow> (Denvalue loaded $$ id = Some (type.Storage v, Storeloc id))" using assms
proof(induct "fmdom ct" rule: fset_induct)
  case empty
  show ?case
  proof(intros)
    fix id v
    assume "ct $$ id = Some (Var v)"
    then have "id |\<in>| fmdom ct" using fmdomI by metis
    then have "id |\<in>| {||}" using empty by simp
    then show "Denvalue loaded $$ id = Some (type.Storage v, Storeloc id)" by blast
  qed
next
  case (insert x xs)
  let ?e_start = "emptyEnv adv c (adde) v'"
  have loaded_def: "ffold (init ct) ?e_start (finsert x xs) = loaded" using insert assms by simp
  show "\<forall>id v. ct $$ id = Some (Var v) \<longrightarrow> Denvalue loaded $$ id = Some (type.Storage v, Storeloc id)"
  proof intros
    fix id v
    assume "ct $$ id = Some (Var v)"
    then show "Denvalue loaded $$ id = Some (type.Storage v, Storeloc id)" using insert
      using ffold_init_fmdom by force
  qed
qed

lemma ffoldInit_var_storage_mapping_rev:
  assumes "ffold (init ct) (emptyEnv adv c (adde) v') (fmdom ct) = loaded"
  shows "\<forall>id v. (Denvalue loaded $$ id = Some (type.Storage v, Storeloc id)) \<longrightarrow> ct $$ id = Some (Var v)" using assms
proof(induct "fmdom ct" rule: fset_induct)
  case empty
  show ?case
  proof(intros)
    fix id v
    assume " Denvalue loaded $$ id = Some (type.Storage v, Storeloc id)"
    then show " ct $$ id = Some (Var v)"
      using assms ffold_init_emptyDen_ran by blast
  qed
next
  case (insert x xs)
  let ?e_start = "emptyEnv adv c (adde) v'"

  have loaded_def: "ffold (init ct) ?e_start (finsert x xs) = loaded" using insert assms by simp
  show "\<forall>id v. Denvalue loaded $$ id = Some (type.Storage v, Storeloc id) \<longrightarrow> ct $$ id = Some (Var v)"
  proof intros
    fix id v
    assume "Denvalue loaded $$ id = Some (type.Storage v, Storeloc id)"
    then show "ct $$ id = Some (Var v)" using insert
      using ffold_init_fmdom
      by (meson ffold_init_emptyDen_ran)
  qed
qed

lemma ffoldInit_var_storage_mapping_eq:
  assumes "ffold (init ct) (emptyEnv adv c (adde) v') (fmdom ct) = loaded"
  shows "\<forall>id v. (Denvalue loaded $$ id = Some (type.Storage v, Storeloc id)) \<longleftrightarrow> ct $$ id = Some (Var v)"
  using ffoldInit_var_storage_mapping_rev ffoldInit_var_storage_mapping assms by blast

end

end
