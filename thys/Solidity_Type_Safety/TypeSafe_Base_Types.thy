section \<open>Type consistency for value types\<close>
theory TypeSafe_Base_Types
  imports TypeSafe_Hashing_Subs
begin

subsection \<open>Ensuring that String @{type \<open>valuetype\<close>} conform to their associated datatype @{type \<open>types\<close>}\<close>
primrec typeCon :: "types \<Rightarrow> valuetype \<Rightarrow> bool"
  where "typeCon (TSInt x) v = checkSInt x v"
  | "typeCon (TUInt x) v = checkUInt x v"
  | "typeCon (TBool) v = checkBool v"
  | "typeCon (TAddr) v = checkAddress v"


lemma typeConNoDots:
  assumes "typeCon t v"
  shows "CHR ''.'' \<notin> set(String.explode v)"
proof(cases t)
  case (TSInt x1)
  then show ?thesis using assms typeCon.simps(1) ShowLIntDot unfolding checkSInt_def by metis
next
  case (TUInt x2)
  then show ?thesis using assms typeCon.simps(2) ShowLIntDot unfolding checkUInt_def by metis
next
  case TBool
  have "CHR ''.'' \<notin> set (literal.explode STR ''True'')" by eval
  moreover have "CHR ''.'' \<notin> set (literal.explode STR ''False'')" by eval
  ultimately show ?thesis using assms typeCon.simps(3) unfolding checkBool_def
    using TBool by auto
next
  case TAddr
  then show ?thesis using assms typeCon.simps(4) checkAddress_def by auto
qed

lemma typeCon_no_sublocation_prefix:
  assumes "typeCon x1 i"
  assumes "hash destl i \<noteq> hash destl x"
  shows "\<not> LSubPrefL2 (hash destl i) (hash destl x)"
  unfolding LSubPrefL2_def
proof
  assume "(\<exists>ia. hash destl i = hash (hash destl x) ia) \<or> hash destl i = hash destl x"
  then show False
  proof
    assume "\<exists>ia. hash destl i = hash (hash destl x) ia"
    then have "\<exists>ia. hash destl i = hash destl (hash x ia)"
      by (simp add: hash_suffixes_associative)
    then have "\<exists>ia. i = (hash x ia)"
      using hash_never_equal_suffix by auto
    then obtain ia where "i = (hash x ia)" by auto
    moreover have "CHR ''.'' \<notin> set(String.explode i)"
    proof(cases x1)
      case (TSInt x1)
      then show ?thesis using typeCon.simps(1)[of x1 i] assms unfolding checkSInt_def using ShowLIntDot by metis
    next
      case (TUInt x2)
      then show ?thesis using typeCon.simps(2)[of x2 i] assms unfolding checkUInt_def using ShowLIntDot by metis
    next
      case TBool
      then have a10:"i = STR ''True'' \<or> i = STR ''False''" using typeCon.simps(3)[of i] assms unfolding checkBool_def by simp
      have "CHR ''.'' \<notin> set (literal.explode STR ''True'') \<and> CHR ''.'' \<notin> set (literal.explode STR ''False'')" by eval
      then show ?thesis using a10 by auto
    next
      case TAddr
      then show ?thesis using typeCon.simps(4)[of i] assms unfolding checkAddress_def by simp
    qed
    ultimately show False using hash_def
      using hash_explode by auto
  next
    assume "hash destl i = hash destl x"
    then show False using assms by simp
  qed
qed

lemma addBalance_Bal:
  assumes "addBalance ad val acc = Some acc'"
  shows "Bal (acc' ad) = ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ad)) + ReadL\<^sub>i\<^sub>n\<^sub>t val)"
  using assms unfolding addBalance_def by (auto simp: Let_def split: if_split_asm)

lemma subBalance_Bal:
  assumes "subBalance ad val acc = Some acc'"
  shows "Bal (acc' ad) = ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ad)) - ReadL\<^sub>i\<^sub>n\<^sub>t val)"
  using assms unfolding subBalance_def by (auto simp: Let_def split: if_split_asm)

text \<open>A successful transfer keeps every balance a valid \<open>uint256\<close>.\<close>

lemma transfer_Bal_typeCon:
  assumes "transfer ads addr val acc = Some acc'"
    and "\<forall>a. typeCon (TUInt b256) (Bal (acc a))"
  shows "typeCon (TUInt b256) (Bal (acc' a))"
proof -
  from assms(1) obtain acc'' where sub: "subBalance ads val acc = Some acc''"
    and add: "addBalance addr val acc'' = Some acc'"
    by (auto simp: transfer_def split: option.splits)
  have "\<forall>ad. 0 \<le> ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ad)) \<and> ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ad)) < 2 ^ 256"
    using assms(2) by (simp add: checkUInt_def)
  then have lim: "0 \<le> ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc' a)) \<and> ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc' a)) < 2 ^ 256"
    using transfer_limit[OF assms(1)] by blast
  have canon: "ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc' a))) = Bal (acc' a)"
  proof (cases "a = addr")
    case True
    then show ?thesis using addBalance_Bal[OF add] Read_ShowL_id by simp
  next
    case False
    then have eq: "Bal (acc' a) = Bal (acc'' a)" using addBalance_eq[OF add] by simp
    show ?thesis
    proof (cases "a = ads")
      case True
      then show ?thesis using eq subBalance_Bal[OF sub] Read_ShowL_id by simp
    next
      case False
      then have "Bal (acc a) = Bal (acc'' a)" using subBalance_eq[OF sub] by metis
      then show ?thesis using eq spec[OF assms(2), of a] by (simp add: checkUInt_def)
    qed
  qed
  show ?thesis using lim canon by (simp add: checkUInt_def)
qed

lemma transfer_subRead:
  assumes "transfer ads addr val acc = Some acc'"
    and "addr \<noteq> ads"
    and "typeCon (TUInt b256) val"
    and "typeCon (TUInt b256) (Bal (acc ads))"
  shows "(Bal (acc' ads)) = ShowL\<^sub>i\<^sub>n\<^sub>t(ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ads)) - ReadL\<^sub>i\<^sub>n\<^sub>t val)"
proof -
  from assms(1) obtain acc''
    where *: "subBalance ads val acc = Some acc''"
      and **: "addBalance addr val acc'' = Some acc'" by (simp add: subBalance_def transfer_def split:if_split_asm)

  then have "ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc'' ads)) = ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ads)) - ReadL\<^sub>i\<^sub>n\<^sub>t val" using subBalance_sub[OF *] by simp
  then have "(Bal (acc'' ads)) = ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ads)) - ReadL\<^sub>i\<^sub>n\<^sub>t val)" using * unfolding subBalance_def
    using "*" subBalance_val1 subBalance_val2 by auto
  moreover from assms(2) have "(Bal (acc' ads)) = (Bal (acc'' ads))" using addBalance_eq[OF **] by simp
  ultimately show ?thesis using Read_ShowL_id assms by simp
qed

lemma transfer_addRead:
  assumes "transfer ads addr val acc = Some acc'"
    and "addr \<noteq> ads"
    and "typeCon (TUInt b256) val"
    and "typeCon (TUInt b256) (Bal (acc addr))"
  shows "(Bal (acc' addr)) = ShowL\<^sub>i\<^sub>n\<^sub>t(ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc addr)) + ReadL\<^sub>i\<^sub>n\<^sub>t val)"
proof -
  from assms(1) obtain acc''
    where *: "subBalance ads val acc = Some acc''"
      and **: "addBalance addr val acc'' = Some acc'" by (simp add: subBalance_def transfer_def split:if_split_asm)
  have ***:"(Bal (acc'' addr)) = (Bal (acc addr))"
    using "*" assms(2) subBalance_eq by presburger
  then have "ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc' addr)) = ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc'' addr)) + ReadL\<^sub>i\<^sub>n\<^sub>t val" using addBalance_add[OF **] by simp
  then have "(Bal (acc' addr)) = ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc addr)) + ReadL\<^sub>i\<^sub>n\<^sub>t val)" using * ** *** unfolding addBalance_def
    by (metis addBalance_Bal[OF **] ***)
  then show ?thesis by simp
qed

lemma transfer_sameRead:
  assumes "transfer ads addr val acc = Some acc'"
    and "addr = ads"
    and "typeCon (TUInt b256) val"
    and "typeCon (TUInt b256) (Bal (acc ads))"
  shows "(Bal (acc' ads)) = (Bal (acc ads))"
proof -
  from assms(1) obtain acc''
    where *: "subBalance ads val acc = Some acc''"
      and **: "addBalance addr val acc'' = Some acc'" by (simp add: subBalance_def transfer_def split:if_split_asm)
  then have "ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ads)) = ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc' ads))" using transfer_same[OF assms(1) ] assms(2) by simp
  moreover have "(Bal (acc'' ads)) = ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc ads)) - ReadL\<^sub>i\<^sub>n\<^sub>t val)" using * subBalance_def
    by (metis subBalance_Bal[OF *])
  moreover from ** have ***:"ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc' ads)) = ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc'' ads)) + ReadL\<^sub>i\<^sub>n\<^sub>t val" using addBalance_add assms(2) by simp
  moreover have "(Bal (acc' addr)) = ShowL\<^sub>i\<^sub>n\<^sub>t (ReadL\<^sub>i\<^sub>n\<^sub>t (Bal (acc'' addr)) +
      ReadL\<^sub>i\<^sub>n\<^sub>t val)" using * ** *** assms(2) unfolding addBalance_def
    by (metis addBalance_Bal[OF **])
  ultimately show ?thesis using Read_ShowL_id assms
    by (simp add: checkUInt_def)
qed

subsection \<open>Creating Signed and Unsigned integers\<close>
lemma checkSIntCreate:
  shows "checkSInt (b) (createSInt b v)" unfolding checkSInt_def using STR_is_int_ShowL Show_ReadL_id createSInt_def createSInt_greater createSInt_less by force

lemma checkUIntCreate:
  shows "checkUInt (b) (createUInt b v)" unfolding checkUInt_def Read_ShowL_id createUInt_def by (simp )


subsection \<open>Compatible types will both satisfy the consistency of a value\<close>
text \<open>If two types are compatible and a value is consistent with the first, it is consistent with the second.\<close>
lemma SameCompTypeCon:
  assumes "comp t t'"
    and "typeCon t v"
  shows "typeCon t' v"
proof (cases t)
  case (TSInt x1)
  then obtain x2 where "t' = TSInt x2 \<and> (bits.to_nat x1 \<le> bits.to_nat x2)" using assms(1) by (cases t'; auto)
  then show ?thesis using assms(2) typeCon.simps(1)[of x1 v ] typeCon.simps(1)[of x2 v ] TSInt checkSIntIncreaseB checkSInt_def by (cases t'; metis)
next
  case (TUInt x2)
  then obtain x3 where "(t' = TUInt x3 \<and> (bits.to_nat x2 \<le> bits.to_nat x3))
                          \<or> (t' = TSInt x3 \<and> (bits.to_nat x2 < bits.to_nat x3))" using assms(1) by (cases t'; auto)
  then show ?thesis using assms(2) typeCon.simps(2) typeCon.simps(1) TUInt checkUIntIncreaseB checkUIntToSInt checkSInt_def checkUInt_def by (cases t'; metis)
next
  case TBool
  then have "t' = t" using comp.elims(2) assms(1) by auto
  then show ?thesis using assms by simp
next
  case TAddr
  then have "t' = t" using comp.elims(2) assms(1) by auto
  then show ?thesis using assms by simp
qed


subsection \<open>Initial values\<close>
text \<open>When a new location is created in Memory, Storage or calldata, or a new variable is created
      then a default initial value is used. These values must satisfy @{const typeCon}, which is what the following
      lemma demonstrates.\<close>
lemma ivalTypeCon:
  assumes "ival t' = v'"
  shows "typeCon t' v'"
proof (cases t')
  case (TSInt x1)
  have a1:"ShowL\<^sub>i\<^sub>n\<^sub>t 0 = STR ''0''" by Solidity_Symbex.solidity_symbex
  then have a10:"ReadL\<^sub>i\<^sub>n\<^sub>t (STR ''0'') = (0::int)" by Solidity_Symbex.solidity_symbex
  then show ?thesis using checkSInt_def[of x1 "STR ''0''"] TSInt assms a1 by simp
next
  case (TUInt x2)
  have a1:"ShowL\<^sub>i\<^sub>n\<^sub>t 0 = STR ''0''" by eval
  then have a10:"ReadL\<^sub>i\<^sub>n\<^sub>t (STR ''0'') = (0::int)" by eval
  then show ?thesis using checkUInt_def[of x2 "STR ''0''"] TUInt assms a1 by simp
next
  case TBool
  have "ShowL\<^sub>b\<^sub>o\<^sub>o\<^sub>l False = STR ''False''" by eval
  then show ?thesis using TBool checkBool_def assms by auto
next
  case TAddr
  then have "v' = STR ''0x0000000000000000000000000000000000000000''" using ival.simps(4) assms by simp
  moreover have "(CHR ''.'' \<notin> set (literal.explode STR ''0x0000000000000000000000000000000000000000''))" by eval
  ultimately show ?thesis using typeCon.simps(4) TAddr checkAddress_def by auto
qed


subsection \<open>Convert is typesafe\<close>
text \<open>Conversion between types preserves type consistency.
      If the string value was consistent with the initial type and a successful conversion
      is performed then the result must be consistent with the new type.\<close>
lemma typeSafeConvert:
  assumes "typeCon t2 v"
    and "convert t2 t' v = Some(v)"
  shows "typeCon t' v"
proof (cases "t2 = t'")
  case True
  then show ?thesis using assms by simp
next
  case False
  then show ?thesis
  proof(cases t2)
    case t2x1:(TSInt x1)
    then show ?thesis
    proof(cases t')
      case (TSInt x1a)
      then have "bits.to_nat(x1) \<le> bits.to_nat(x1a)" using assms(2) convert.simps(1)[of x1 x1a v] by (metis TSInt not_Some_eq t2x1)
      then show ?thesis using assms(1) typeCon.simps(1)[of x1 v] typeCon.simps(1)[of x1a v] checkSIntIncreaseB checkSInt_def
        by (metis TSInt t2x1)
    next
      case (TUInt x2)
      then have "convert (TSInt x1) (TUInt x2) v = None" using convert.simps by simp
      then have False using assms t2x1 TUInt by simp
      then show ?thesis by simp
    next
      case TBool
      then have "convert (TSInt x1) TBool v = None" using convert.simps by simp
      then have False using assms t2x1 TBool by simp
      then show ?thesis by simp
    next
      case TAddr
      then have "convert (TSInt x1) TAddr v = None" using convert.simps by simp
      then have False using assms t2x1 TAddr by simp
      then show ?thesis by simp
    qed
  next
    case t2x2:(TUInt x2)
    then show ?thesis
    proof(cases t')
      case (TSInt x1a)
      then have "bits.to_nat(x2) < bits.to_nat(x1a)" using assms(2) convert.simps(1)[of x2 x1a v] by (metis convert.simps(3) option.distinct(1) t2x2)
      then show ?thesis using assms(1) typeCon.simps(2)[of x2 v] typeCon.simps(1)[of x1a v] checkUIntToSInt checkSInt_def checkUInt_def TSInt assms(2) convert.simps(3) t2x2 by force
    next
      case (TUInt x2a)
      then have "bits.to_nat(x2)\<le>bits.to_nat(x2a)" using assms(2) convert.simps(2)[of x2 x2a v] by (metis option.discI t2x2)
      then show ?thesis using checkUIntIncreaseB assms t2x2 TUInt typeCon.simps(2) convert.simps(2) checkUInt_def by auto
    next
      case TBool
      then have "convert (TUInt x2) TBool v = None" using convert.simps by simp
      then have False using assms t2x2 TBool by simp
      then show ?thesis by simp
    next
      case TAddr
      then have "convert (TUInt x2) TAddr v = None" using convert.simps by simp
      then have False using assms t2x2 TAddr by simp
      then show ?thesis by simp
    qed
  next
    case TBool
    then have "t' \<noteq> TBool" using False by simp
    then have "convert t2 t' v = None" using convert.simps by (metis TBool types.exhaust)
    then have False using assms by simp
    then show ?thesis by simp
  next
    case TAddr
    then have "t' \<noteq> TAddr" using False by simp
    then have "convert t2 t' v = None" using convert.simps by (metis TAddr types.exhaust)
    then have False using assms by simp
    then show ?thesis by simp
  qed
qed


end
