theory HIT_Open_Boundary_Check
  imports HIT_Canonical_Normal_Forms
begin

section \<open>Finite open-term boundary checking\<close>

text \<open>
  The semantic predicate \<^const>\<open>typed_coherent_methods\<close> ranges over every
  dimension context, term context, and typed constructor instance.  Its
  boundary obligation can instead be discharged once per path constructor.
  We append fresh variables for that constructor's arguments to the ambient
  term context and check the two open faces there.  Simultaneous substitution
  then transports each open check to every typed instance.

  The resulting predicate is a finite family of typing and joinability
  obligations.  A second formulation compares the canonical normal forms of
  each pair; the two formulations are equivalent for the typed open terms.
  The canonical normalizer uses Hilbert choice, so neither formulation is
  presented as executable code.  The theorem below establishes the soundness
  bridge from the finite open obligations to the extensional safety predicate
  used by the rest of the development.
\<close>

definition open_args :: "ty list \<Rightarrow> argspec list \<Rightarrow> tm list" where
  "open_args G ss =
    map (\<lambda>i. Var (length G + i)) [0..<length ss]"

definition open_inst :: "ty list \<Rightarrow> tm list \<Rightarrow> nat \<Rightarrow> tm" where
  "open_inst G as i =
    (if i < length G then Var i
     else if i - length G < length as then as ! (i - length G)
     else Var i)"

definition open_face ::
  "sigenv \<Rightarrow> ty list \<Rightarrow> nat \<Rightarrow> ty \<Rightarrow>
    tm list \<Rightarrow> tm list \<Rightarrow> nat \<Rightarrow> dim \<Rightarrow> tm"
where
  "open_face S G h C pms lms k d =
    apps (dsubst S 0 d (lms ! k))
      (elimArgs h C pms lms (lcons (S h) ! k)
        (open_args G (lcons (S h) ! k)))"

definition open_endpoint ::
  "sigenv \<Rightarrow> ty list \<Rightarrow> nat \<Rightarrow> ty \<Rightarrow>
    tm list \<Rightarrow> tm list \<Rightarrow> nat \<Rightarrow> endpt \<Rightarrow> tm"
where
  "open_endpoint S G h C pms lms k e =
    elimEnd S h C pms lms (open_args G (lcons (S h) ! k)) e"

definition boundary_check_base ::
  "sigenv \<Rightarrow> nat set \<Rightarrow> ty list \<Rightarrow> nat \<Rightarrow> ty \<Rightarrow>
    tm list \<Rightarrow> tm list \<Rightarrow> bool"
where
  "boundary_check_base S D G h C pms lms \<longleftrightarrow>
    wf_sigenv S \<and>
    0 \<notin> D \<and>
    length pms = length (pcons (S h)) \<and>
    length lms = length (lcons (S h)) \<and>
    (\<forall>k < length pms.
      wt S D G (pms ! k) (methodTy h C (pcons (S h) ! k))) \<and>
    (\<forall>k < length lms.
      wt S (insert 0 D) G (lms ! k)
        (methodTy h C (lcons (S h) ! k)))"

definition open_boundary_check ::
  "sigenv \<Rightarrow> nat set \<Rightarrow> ty list \<Rightarrow> nat \<Rightarrow> ty \<Rightarrow>
    tm list \<Rightarrow> tm list \<Rightarrow> bool"
where
  "open_boundary_check S D G h C pms lms \<longleftrightarrow>
    wf_sigenv S \<and>
    0 \<notin> D \<and>
    length pms = length (pcons (S h)) \<and>
    length lms = length (lcons (S h)) \<and>
    (\<forall>k < length pms.
      wt S D G (pms ! k) (methodTy h C (pcons (S h) ! k))) \<and>
    (\<forall>k < length lms.
      wt S (insert 0 D) G (lms ! k)
        (methodTy h C (lcons (S h) ! k))) \<and>
    (\<forall>k < length (lcons (S h)).
      joinable S
        (open_face S G h C pms lms k D0)
        (open_endpoint S G h C pms lms k
          (fst (lends (S h) ! k))) \<and>
      joinable S
        (open_face S G h C pms lms k D1)
        (open_endpoint S G h C pms lms k
          (snd (lends (S h) ! k))))"

definition normal_boundary_check ::
  "sigenv \<Rightarrow> nat set \<Rightarrow> ty list \<Rightarrow> nat \<Rightarrow> ty \<Rightarrow>
    tm list \<Rightarrow> tm list \<Rightarrow> bool"
where
  "normal_boundary_check S D G h C pms lms \<longleftrightarrow>
    boundary_check_base S D G h C pms lms \<and>
    (\<forall>k < length (lcons (S h)).
      canonical_nf S (open_face S G h C pms lms k D0) =
        canonical_nf S
          (open_endpoint S G h C pms lms k
            (fst (lends (S h) ! k))) \<and>
      canonical_nf S (open_face S G h C pms lms k D1) =
        canonical_nf S
          (open_endpoint S G h C pms lms k
            (snd (lends (S h) ! k))))"

definition open_context ::
  "ty list \<Rightarrow> nat \<Rightarrow> argspec list \<Rightarrow> ty list"
where
  "open_context G h ss = G @ map (argTy h) ss"

lemma open_args_length [simp]:
  "length (open_args G ss) = length ss"
  by (simp add: open_args_def)

lemma open_args_nth:
  assumes "i < length ss"
  shows "open_args G ss ! i = Var (length G + i)"
  using assms by (simp add: open_args_def)

lemma open_inst_prefix:
  assumes "i < length G"
  shows "open_inst G as i = Var i"
  using assms by (simp add: open_inst_def)

lemma psubst_open_args:
  assumes "length as = length ss"
  shows "map (psubst (open_inst G as)) (open_args G ss) = as"
proof (rule nth_equalityI)
  show "length (map (psubst (open_inst G as)) (open_args G ss)) =
      length as"
    using assms by simp
next
  fix i
  assume i: "i < length
      (map (psubst (open_inst G as)) (open_args G ss))"
  then have iss: "i < length ss" by simp
  then have ias: "i < length as" using assms by simp
  show "(map (psubst (open_inst G as)) (open_args G ss)) ! i = as ! i"
    using iss ias by (simp add: open_args_nth open_inst_def)
qed

lemma up_sub_prefix:
  assumes "\<forall>i < length G. s i = Var i"
  shows "\<forall>i < length (A # G). up_sub s i = Var i"
  using assms
  by (intro allI impI) (case_tac i; simp)

theorem wt_context_append:
  assumes "wt S D G t A"
  shows "wt S D (G @ H) t A"
  using assms
proof (induct rule: wt.induct)
  case (wtVar i G D)
  have i: "i < length (G @ H)" using wtVar by simp
  have nth: "(G @ H) ! i = G ! i"
    using wtVar by (simp add: nth_append)
  from wt.wtVar[OF i] nth show ?case by simp
next
  case wtLam
  then show ?case by (auto intro: wt.wtLam)
next
  case wtApp
  then show ?case by (auto intro: wt.wtApp)
next
  case wtPCon
  then show ?case by (auto intro!: wt.wtPCon)
next
  case wtLCon
  then show ?case by (auto intro!: wt.wtLCon)
next
  case wtElim
  then show ?case by (auto intro!: wt.wtElim)
qed

lemma open_args_typed:
  assumes "i < length ss"
  shows "wt S D (open_context G h ss)
    (open_args G ss ! i) (argTy h (ss ! i))"
proof -
  have index: "length G + i < length (open_context G h ss)"
    using assms by (simp add: open_context_def)
  have nth: "open_context G h ss ! (length G + i) =
      argTy h (ss ! i)"
    using assms by (simp add: open_context_def nth_append)
  have "wt S D (open_context G h ss)
      (Var (length G + i))
      (open_context G h ss ! (length G + i))"
    by (rule wt.wtVar[OF index])
  with nth open_args_nth[OF assms] show ?thesis by simp
qed

lemma psubst_identity_wt:
  assumes typed: "wt S D G t A"
    and fixed: "\<forall>i < length G. s i = Var i"
  shows "psubst s t = t"
  using typed fixed
proof (induct arbitrary: s rule: wt.induct)
  case (wtVar i G D)
  then show ?case by simp
next
  case (wtLam D A G t B)
  have prefix: "\<forall>i < length (A # G). up_sub s i = Var i"
    by (rule up_sub_prefix[OF wtLam.prems])
  from wtLam(2)[OF prefix] show ?case by simp
next
  case (wtApp D G t A B u)
  then show ?case by simp
next
  case (wtPCon k h as D G)
  have args: "map (psubst s) as = as"
  proof (rule map_idI)
    fix x
    assume "x \<in> set as"
    then obtain i where i: "i < length as" and x: "x = as ! i"
      by (auto simp: in_set_conv_nth)
    have "psubst s (as ! i) = as ! i"
      using wtPCon i by auto
    with x show "psubst s x = x" by simp
  qed
  then show ?case by simp
next
  case (wtLCon j D k h as G)
  have args: "map (psubst s) as = as"
  proof (rule map_idI)
    fix x
    assume "x \<in> set as"
    then obtain i where i: "i < length as" and x: "x = as ! i"
      by (auto simp: in_set_conv_nth)
    have "psubst s (as ! i) = as ! i"
      using wtLCon i by auto
    with x show "psubst s x = x" by simp
  qed
  then show ?case by simp
next
  case (wtElim D G t h pms lms C)
  have scrutinee: "psubst s t = t"
    by (rule wtElim(2)[OF wtElim.prems])
  have point_methods: "map (psubst s) pms = pms"
  proof (rule map_idI)
    fix x
    assume "x \<in> set pms"
    then obtain i where i: "i < length pms" and x: "x = pms ! i"
      by (auto simp: in_set_conv_nth)
    have "psubst s (pms ! i) = pms ! i"
      using wtElim i by auto
    with x show "psubst s x = x" by simp
  qed
  have path_methods: "map (psubst s) lms = lms"
  proof (rule map_idI)
    fix x
    assume "x \<in> set lms"
    then obtain i where i: "i < length lms" and x: "x = lms ! i"
      by (auto simp: in_set_conv_nth)
    have "psubst s (lms ! i) = lms ! i"
      using wtElim i by auto
    with x show "psubst s x = x" by simp
  qed
  show ?case using point_methods path_methods scrutinee by simp
qed

lemma open_inst_regular:
  assumes args: "\<forall>i < length as. \<exists>A. wt S D H (as ! i) A"
  shows "regular S (open_inst G as i)"
proof (cases "i < length G")
  case True
  then show ?thesis by (simp add: open_inst_def)
next
  assume not_prefix: "\<not> i < length G"
  show ?thesis
  proof (cases "i - length G < length as")
    assume in_args: "i - length G < length as"
    then obtain A where "wt S D H (as ! (i - length G)) A"
      using args by blast
    then show ?thesis
      using not_prefix in_args regular_wt by (simp add: open_inst_def)
  next
    assume not_args: "\<not> i - length G < length as"
    with not_prefix show ?thesis by (simp add: open_inst_def)
  qed
qed

lemma open_inst_dclosed0:
  assumes zero: "0 \<notin> D"
    and args: "\<forall>i < length as. \<exists>A. wt S D H (as ! i) A"
  shows "dclosed0 S (open_inst G as i)"
proof (cases "i < length G")
  case True
  then show ?thesis by (simp add: open_inst_def)
next
  assume not_prefix: "\<not> i < length G"
  show ?thesis
  proof (cases "i - length G < length as")
    assume in_args: "i - length G < length as"
    then obtain A where typed:
        "wt S D H (as ! (i - length G)) A"
      using args by blast
    have "\<forall>j. dsubst S 0 (DVar j) (as ! (i - length G)) =
        as ! (i - length G)"
      using wt_dsubst_fresh[OF typed zero] by blast
    then show ?thesis
      using not_prefix in_args
      unfolding dclosed0_def open_inst_def by simp
  next
    assume not_args: "\<not> i - length G < length as"
    with not_prefix show ?thesis by (simp add: open_inst_def)
  qed
qed

lemma reds_psubst_dclosed:
  assumes steps: "reds S t u"
    and reg: "regular S t"
    and env_reg: "\<And>i. regular S (s i)"
    and env_closed: "\<And>i. dclosed0 S (s i)"
  shows "reds S (psubst s t) (psubst s u)"
  using steps reg
proof (induct rule: rtranclp_induct)
  case base
  show ?case by simp
next
  case (step y z)
  have yreg: "regular S y"
    by (rule regular_reds[OF step.hyps(1) step.prems])
  have yz: "red S (psubst s y) (psubst s z)"
    by (rule red_psubst_dclosed[
          OF step.hyps(2) yreg env_reg env_closed])
  from step.hyps(3)[OF step.prems] yz show ?case
    by (rule rtranclp.rtrancl_into_rtrancl)
qed

lemma joinable_psubst_dclosed:
  assumes join: "joinable S t u"
    and treg: "regular S t"
    and ureg: "regular S u"
    and env_reg: "\<And>i. regular S (s i)"
    and env_closed: "\<And>i. dclosed0 S (s i)"
  shows "joinable S (psubst s t) (psubst s u)"
proof -
  from join obtain v where tv: "reds S t v" and uv: "reds S u v"
    unfolding joinable_def by blast
  have "reds S (psubst s t) (psubst s v)"
    by (rule reds_psubst_dclosed[OF tv treg env_reg env_closed])
  moreover have "reds S (psubst s u) (psubst s v)"
    by (rule reds_psubst_dclosed[OF uv ureg env_reg env_closed])
  ultimately show ?thesis unfolding joinable_def by blast
qed

lemma psubst_instE:
  assumes endpoint: "wf_endpt S h ss e A"
    and len: "length xs = length ss"
  shows "psubst s (instE h xs e) =
    instE h (map (psubst s) xs) e"
  using endpoint len
proof (induct rule: wf_endpt.induct)
  case (wfEArg i)
  then show ?case by simp
next
  case (wfECon k es)
  have inst:
      "map (psubst s \<circ> instE h xs) es =
       map (instE h (map (psubst s) xs)) es"
  proof (rule nth_equalityI)
    show "length (map (psubst s \<circ> instE h xs) es) =
        length (map (instE h (map (psubst s) xs)) es)"
      by simp
  next
    fix i
    assume i: "i < length (map (psubst s \<circ> instE h xs) es)"
    then have "i < length es" by simp
    with wfECon show "(map (psubst s \<circ> instE h xs) es) ! i =
        (map (instE h (map (psubst s) xs)) es) ! i"
      by simp
  qed
  then show ?case by (simp add: map_map)
qed

lemma psubst_elimEnd:
  assumes endpoint: "wf_endpt S h ss e A"
    and len: "length xs = length ss"
    and plen: "length pms = length (pcons (S h))"
  shows "psubst s (elimEnd S h C pms lms xs e) =
    elimEnd S h C (map (psubst s) pms) (map (psubst s) lms)
      (map (psubst s) xs) e"
  using endpoint
proof cases
  case (wfEArg i)
  then show ?thesis using len by simp
next
  case (wfECon k es)
  have kpm: "k < length pms" using wfECon plen by simp
  have inst:
      "map (psubst s \<circ> instE h xs) es =
       map (instE h (map (psubst s) xs)) es"
  proof (rule nth_equalityI)
    show "length (map (psubst s \<circ> instE h xs) es) =
        length (map (instE h (map (psubst s) xs)) es)"
      by simp
  next
    fix i
    assume i: "i < length (map (psubst s \<circ> instE h xs) es)"
    then have ies: "i < length es" by simp
    have ep: "wf_endpt S h ss (es ! i)
        (argTy h (pcons (S h) ! k ! i))"
      using wfECon ies by blast
    from psubst_instE[OF ep len] ies
    show "(map (psubst s \<circ> instE h xs) es) ! i =
        (map (instE h (map (psubst s) xs)) es) ! i"
      by simp
  qed
  have mapped:
      "map (psubst s)
        (elimArgs h C pms lms (pcons (S h) ! k)
          (map (instE h xs) es)) =
       elimArgs h C (map (psubst s) pms) (map (psubst s) lms)
         (pcons (S h) ! k)
         (map (instE h (map (psubst s) xs)) es)"
    by (simp add: psubst_elimArgs map_map inst)
  show ?thesis
    using wfECon kpm mapped by simp
qed

lemma regular_instE:
  assumes endpoint: "wf_endpt S h ss e A"
    and len: "length as = length ss"
    and args: "list_all (regular S) as"
  shows "regular S (instE h as e)"
  using endpoint
proof (induct rule: wf_endpt.induct)
  case (wfEArg i)
  then show ?case
    using len args by (auto simp: list_all_iff)
next
  case (wfECon k es)
  have inst: "list_all (regular S) (map (instE h as) es)"
  proof (unfold list_all_iff, intro ballI)
    fix x
    assume "x \<in> set (map (instE h as) es)"
    then obtain e where eset: "e \<in> set es"
      and x: "x = instE h as e" by auto
    then obtain i where i: "i < length es" and e: "e = es ! i"
      by (auto simp: in_set_conv_nth)
    have "regular S (instE h as (es ! i))"
      using wfECon i by auto
    with x e show "regular S x" by simp
  qed
  show ?case using wfECon inst by simp
qed

lemma regular_elimEnd:
  assumes endpoint: "wf_endpt S h ss e A"
    and len: "length as = length ss"
    and args: "list_all (regular S) as"
    and plen: "length pms = length (pcons (S h))"
    and llen: "length lms = length (lcons (S h))"
    and pms: "list_all (regular S) pms"
    and lms: "list_all (regular S) lms"
  shows "regular S (elimEnd S h C pms lms as e)"
  using endpoint
proof cases
  case (wfEArg i)
  have "regular S (as ! i)"
    using wfEArg len args by (auto simp: list_all_iff)
  then show ?thesis using plen llen pms lms wfEArg by simp
next
  case (wfECon k es)
  have method: "regular S (pms ! k)"
    using wfECon plen pms by (auto simp: list_all_iff)
  have inst: "list_all (regular S) (map (instE h as) es)"
  proof (unfold list_all_iff, intro ballI)
    fix x
    assume "x \<in> set (map (instE h as) es)"
    then obtain e where eset: "e \<in> set es"
      and x: "x = instE h as e" by auto
    then obtain i where i: "i < length es" and e: "e = es ! i"
      by (auto simp: in_set_conv_nth)
    have ep: "wf_endpt S h ss (es ! i)
        (argTy h (pcons (S h) ! k ! i))"
      using wfECon i by blast
    have "regular S (instE h as (es ! i))"
      by (rule regular_instE[OF ep len args])
    with x e show "regular S x" by simp
  qed
  have eargs: "list_all (regular S)
      (elimArgs h C pms lms (pcons (S h) ! k)
        (map (instE h as) es))"
    by (rule regular_elimArgs[OF plen llen pms lms inst])
  show ?thesis
    using wfECon method eargs by (simp add: regular_apps)
qed

lemma typed_list_regular:
  assumes "\<forall>i < length xs. \<exists>A. wt S D G (xs ! i) A"
  shows "list_all (regular S) xs"
  unfolding list_all_iff
proof
  fix x
  assume "x \<in> set xs"
  then obtain i where i: "i < length xs" and x: "x = xs ! i"
    by (auto simp: in_set_conv_nth)
  from assms[rule_format, OF i] obtain A where
    "wt S D G (xs ! i) A" by blast
  then have "regular S (xs ! i)" by (rule regular_wt)
  with x show "regular S x" by simp
qed

lemma map_psubst_identity_wt:
  assumes typed: "\<forall>i < length xs. \<exists>A. wt S D G (xs ! i) A"
    and fixed: "\<forall>i < length G. s i = Var i"
  shows "map (psubst s) xs = xs"
proof (rule map_idI)
  fix x
  assume "x \<in> set xs"
  then obtain i where i: "i < length xs" and x: "x = xs ! i"
    by (auto simp: in_set_conv_nth)
  from typed[rule_format, OF i] obtain A where
    "wt S D G (xs ! i) A" by blast
  from psubst_identity_wt[OF this fixed] x
  show "psubst s x = x" by simp
qed

lemma open_boundary_check_base:
  assumes "open_boundary_check S D G h C pms lms"
  shows "boundary_check_base S D G h C pms lms"
  using assms
  unfolding open_boundary_check_def boundary_check_base_def by blast

theorem open_face_typed:
  assumes base: "boundary_check_base S D G h C pms lms"
    and k: "k < length (lcons (S h))"
    and face: "d = D0 \<or> d = D1"
  shows "wt S D (open_context G h (lcons (S h) ! k))
    (open_face S G h C pms lms k d) C"
proof -
  from base have wf: "wf_sigenv S"
    and zero: "0 \<notin> D"
    and plen: "length pms = length (pcons (S h))"
    and llen: "length lms = length (lcons (S h))"
    and ptyped: "\<forall>i < length pms.
      wt S D G (pms ! i) (methodTy h C (pcons (S h) ! i))"
    and ltyped: "\<forall>i < length lms.
      wt S (insert 0 D) G (lms ! i)
        (methodTy h C (lcons (S h) ! i))"
    unfolding boundary_check_base_def by blast+
  let ?ss = "lcons (S h) ! k"
  let ?K = "open_context G h ?ss"
  have klm: "k < length lms" using k llen by simp
  have ptyped_open: "\<forall>i < length pms.
      wt S D ?K (pms ! i) (methodTy h C (pcons (S h) ! i))"
    unfolding open_context_def
    using ptyped by (blast intro: wt_context_append)
  have ltyped_open: "\<forall>i < length lms.
      wt S (insert 0 D) ?K (lms ! i)
        (methodTy h C (lcons (S h) ! i))"
    unfolding open_context_def
    using ltyped by (blast intro: wt_context_append)
  have args: "\<forall>i < length ?ss.
      wt S D ?K (open_args G ?ss ! i) (argTy h (?ss ! i))"
    using open_args_typed by blast
  have recursive: "\<And>a. wt S D ?K a (Hit h) \<Longrightarrow>
      wt S D ?K (HElim h C pms lms a) C"
    by (intro wt.wtElim[OF _ plen llen ptyped_open ltyped_open])
  have lm: "wt S (insert 0 D) ?K (lms ! k) (methodTy h C ?ss)"
    using ltyped_open klm by simp
  have method: "wt S D ?K (dsubst S 0 d (lms ! k))
      (methodTy h C ?ss)"
  proof (rule disjE[OF face])
    assume d: "d = D0"
    have "wt S (dctx_subst 0 D0 (insert 0 D)) ?K
        (dsubst S 0 D0 (lms ! k)) (methodTy h C ?ss)"
      by (rule wt_dimension_subst[OF lm wf])
    with zero d show ?thesis by (simp add: dctx_subst_def)
  next
    assume d: "d = D1"
    have "wt S (dctx_subst 0 D1 (insert 0 D)) ?K
        (dsubst S 0 D1 (lms ! k)) (methodTy h C ?ss)"
      by (rule wt_dimension_subst[OF lm wf])
    with zero d show ?thesis by (simp add: dctx_subst_def)
  qed
  show ?thesis
    unfolding open_face_def
    by (rule wt_apps_elimArgs[
          OF recursive open_args_length args method])
qed

theorem open_endpoint_typed:
  assumes base: "boundary_check_base S D G h C pms lms"
    and k: "k < length (lcons (S h))"
    and endpoint: "wf_endpt S h (lcons (S h) ! k) e (Hit h)"
  shows "wt S D (open_context G h (lcons (S h) ! k))
    (open_endpoint S G h C pms lms k e) C"
proof -
  from base have plen: "length pms = length (pcons (S h))"
    and llen: "length lms = length (lcons (S h))"
    and ptyped: "\<forall>i < length pms.
      wt S D G (pms ! i) (methodTy h C (pcons (S h) ! i))"
    and ltyped: "\<forall>i < length lms.
      wt S (insert 0 D) G (lms ! i)
        (methodTy h C (lcons (S h) ! i))"
    unfolding boundary_check_base_def by blast+
  let ?ss = "lcons (S h) ! k"
  let ?K = "open_context G h ?ss"
  have ptyped_open: "\<forall>i < length pms.
      wt S D ?K (pms ! i) (methodTy h C (pcons (S h) ! i))"
    unfolding open_context_def
    using ptyped by (blast intro: wt_context_append)
  have ltyped_open: "\<forall>i < length lms.
      wt S (insert 0 D) ?K (lms ! i)
        (methodTy h C (lcons (S h) ! i))"
    unfolding open_context_def
    using ltyped by (blast intro: wt_context_append)
  have args: "\<forall>i < length (open_args G ?ss).
      wt S D ?K (open_args G ?ss ! i) (argTy h (?ss ! i))"
    using open_args_typed by simp
  show ?thesis
    unfolding open_endpoint_def
    by (rule wt_elimEnd[
          OF endpoint open_args_length args
            plen llen ptyped_open ltyped_open])
qed

lemma open_joinable_iff_canonical_nf_eq:
  assumes base: "boundary_check_base S D G h C pms lms"
    and k: "k < length (lcons (S h))"
    and endpoint: "wf_endpt S h (lcons (S h) ! k) e (Hit h)"
    and face: "d = D0 \<or> d = D1"
  shows "joinable S
      (open_face S G h C pms lms k d)
      (open_endpoint S G h C pms lms k e) \<longleftrightarrow>
    canonical_nf S (open_face S G h C pms lms k d) =
      canonical_nf S (open_endpoint S G h C pms lms k e)"
  by (rule typed_joinable_iff_canonical_nf_eq[
        OF open_face_typed[OF base k face]
          open_endpoint_typed[OF base k endpoint]])

theorem normal_boundary_check_iff_open_boundary_check:
  "normal_boundary_check S D G h C pms lms \<longleftrightarrow>
    open_boundary_check S D G h C pms lms"
proof
  assume normal: "normal_boundary_check S D G h C pms lms"
  then have base: "boundary_check_base S D G h C pms lms"
    and equal:
      "\<forall>k < length (lcons (S h)).
        canonical_nf S (open_face S G h C pms lms k D0) =
          canonical_nf S
            (open_endpoint S G h C pms lms k
              (fst (lends (S h) ! k))) \<and>
        canonical_nf S (open_face S G h C pms lms k D1) =
          canonical_nf S
            (open_endpoint S G h C pms lms k
              (snd (lends (S h) ! k)))"
    unfolding normal_boundary_check_def by blast+
  from base have wf: "wf_sigenv S"
    unfolding boundary_check_base_def by blast
  have sig: "wf_hsig S h"
    using wf unfolding wf_sigenv_def by blast
  have obligations:
      "\<forall>k < length (lcons (S h)).
        joinable S
          (open_face S G h C pms lms k D0)
          (open_endpoint S G h C pms lms k
            (fst (lends (S h) ! k))) \<and>
        joinable S
          (open_face S G h C pms lms k D1)
          (open_endpoint S G h C pms lms k
            (snd (lends (S h) ! k)))"
  proof (intro allI impI)
    fix k
    assume k: "k < length (lcons (S h))"
    have zero:
        "joinable S
          (open_face S G h C pms lms k D0)
          (open_endpoint S G h C pms lms k
            (fst (lends (S h) ! k))) \<longleftrightarrow>
        canonical_nf S (open_face S G h C pms lms k D0) =
          canonical_nf S
            (open_endpoint S G h C pms lms k
              (fst (lends (S h) ! k)))"
      by (rule open_joinable_iff_canonical_nf_eq[
            OF base k wf_hsig_lhs[OF sig k]]) simp
    have one:
        "joinable S
          (open_face S G h C pms lms k D1)
          (open_endpoint S G h C pms lms k
            (snd (lends (S h) ! k))) \<longleftrightarrow>
        canonical_nf S (open_face S G h C pms lms k D1) =
          canonical_nf S
            (open_endpoint S G h C pms lms k
              (snd (lends (S h) ! k)))"
      by (rule open_joinable_iff_canonical_nf_eq[
            OF base k wf_hsig_rhs[OF sig k]]) simp
    from equal[rule_format, OF k] zero one
    show "joinable S
        (open_face S G h C pms lms k D0)
        (open_endpoint S G h C pms lms k
          (fst (lends (S h) ! k))) \<and>
      joinable S
        (open_face S G h C pms lms k D1)
        (open_endpoint S G h C pms lms k
          (snd (lends (S h) ! k)))"
      by blast
  qed
  from base obligations show
      "open_boundary_check S D G h C pms lms"
    unfolding boundary_check_base_def open_boundary_check_def by blast
next
  assume checked: "open_boundary_check S D G h C pms lms"
  have base: "boundary_check_base S D G h C pms lms"
    by (rule open_boundary_check_base[OF checked])
  from checked have joins:
      "\<forall>k < length (lcons (S h)).
        joinable S
          (open_face S G h C pms lms k D0)
          (open_endpoint S G h C pms lms k
            (fst (lends (S h) ! k))) \<and>
        joinable S
          (open_face S G h C pms lms k D1)
          (open_endpoint S G h C pms lms k
            (snd (lends (S h) ! k)))"
    unfolding open_boundary_check_def by blast
  from base have wf: "wf_sigenv S"
    unfolding boundary_check_base_def by blast
  have sig: "wf_hsig S h"
    using wf unfolding wf_sigenv_def by blast
  have equal:
      "\<forall>k < length (lcons (S h)).
        canonical_nf S (open_face S G h C pms lms k D0) =
          canonical_nf S
            (open_endpoint S G h C pms lms k
              (fst (lends (S h) ! k))) \<and>
        canonical_nf S (open_face S G h C pms lms k D1) =
          canonical_nf S
            (open_endpoint S G h C pms lms k
              (snd (lends (S h) ! k)))"
  proof (intro allI impI)
    fix k
    assume k: "k < length (lcons (S h))"
    have zero:
        "joinable S
          (open_face S G h C pms lms k D0)
          (open_endpoint S G h C pms lms k
            (fst (lends (S h) ! k))) \<longleftrightarrow>
        canonical_nf S (open_face S G h C pms lms k D0) =
          canonical_nf S
            (open_endpoint S G h C pms lms k
              (fst (lends (S h) ! k)))"
      by (rule open_joinable_iff_canonical_nf_eq[
            OF base k wf_hsig_lhs[OF sig k]]) simp
    have one:
        "joinable S
          (open_face S G h C pms lms k D1)
          (open_endpoint S G h C pms lms k
            (snd (lends (S h) ! k))) \<longleftrightarrow>
        canonical_nf S (open_face S G h C pms lms k D1) =
          canonical_nf S
            (open_endpoint S G h C pms lms k
              (snd (lends (S h) ! k)))"
      by (rule open_joinable_iff_canonical_nf_eq[
            OF base k wf_hsig_rhs[OF sig k]]) simp
    from joins[rule_format, OF k] zero one
    show "canonical_nf S (open_face S G h C pms lms k D0) =
        canonical_nf S
          (open_endpoint S G h C pms lms k
            (fst (lends (S h) ! k))) \<and>
      canonical_nf S (open_face S G h C pms lms k D1) =
        canonical_nf S
          (open_endpoint S G h C pms lms k
            (snd (lends (S h) ! k)))"
      by blast
  qed
  from base equal show "normal_boundary_check S D G h C pms lms"
    unfolding normal_boundary_check_def by blast
qed

theorem open_boundary_check_sound:
  assumes check: "open_boundary_check S D G h C pms lms"
  shows "typed_coherent_methods S h C pms lms"
proof -
  from check have wf: "wf_sigenv S"
    and zeroD: "0 \<notin> D"
    and plen: "length pms = length (pcons (S h))"
    and llen: "length lms = length (lcons (S h))"
    and ptyped: "\<forall>k < length pms.
      wt S D G (pms ! k) (methodTy h C (pcons (S h) ! k))"
    and ltyped: "\<forall>k < length lms.
      wt S (insert 0 D) G (lms ! k)
        (methodTy h C (lcons (S h) ! k))"
    and open_obligations:
      "\<forall>k < length (lcons (S h)).
        joinable S
          (open_face S G h C pms lms k D0)
          (open_endpoint S G h C pms lms k
            (fst (lends (S h) ! k))) \<and>
        joinable S
          (open_face S G h C pms lms k D1)
          (open_endpoint S G h C pms lms k
            (snd (lends (S h) ! k)))"
    unfolding open_boundary_check_def by blast+
  have sig: "wf_hsig S h"
    using wf unfolding wf_sigenv_def by blast
  have pms_reg: "list_all (regular S) pms"
  proof (rule typed_list_regular)
    show "\<forall>i < length pms. \<exists>A. wt S D G (pms ! i) A"
      using ptyped by blast
  qed
  have lms_reg: "list_all (regular S) lms"
  proof (rule typed_list_regular)
    show "\<forall>i < length lms.
        \<exists>A. wt S (insert 0 D) G (lms ! i) A"
      using ltyped by blast
  qed
  show ?thesis
    unfolding typed_coherent_methods_def
  proof (intro conjI)
    show "length pms = length (pcons (S h))" by (rule plen)
  next
    show "length lms = length (lcons (S h))" by (rule llen)
  next
    show "\<forall>k E H as.
        k < length (lcons (S h)) \<longrightarrow>
        length as = length (lcons (S h) ! k) \<longrightarrow>
        0 \<notin> E \<longrightarrow>
        (\<forall>i < length as.
          wt S E H (as ! i)
            (argTy h (lcons (S h) ! k ! i))) \<longrightarrow>
        joinable S
          (apps (dsubst S 0 D0 (lms ! k))
            (elimArgs h C pms lms (lcons (S h) ! k) as))
          (elimEnd S h C pms lms as
            (fst (lends (S h) ! k))) \<and>
        joinable S
          (apps (dsubst S 0 D1 (lms ! k))
            (elimArgs h C pms lms (lcons (S h) ! k) as))
          (elimEnd S h C pms lms as
            (snd (lends (S h) ! k)))"
    proof (intro allI impI)
      fix k E H as
      assume k: "k < length (lcons (S h))"
        and len: "length as = length (lcons (S h) ! k)"
        and zeroE: "0 \<notin> E"
        and args: "\<forall>i < length as.
          wt S E H (as ! i) (argTy h (lcons (S h) ! k ! i))"
      let ?ss = "lcons (S h) ! k"
      let ?oas = "open_args G ?ss"
      let ?env = "open_inst G as"
      have klm: "k < length lms" using k llen by simp
    have prefix: "\<forall>i < length G. ?env i = Var i"
      using open_inst_prefix by blast
    have arg_exists: "\<forall>i < length as. \<exists>A. wt S E H (as ! i) A"
      using args by blast
    have env_reg: "\<And>i. regular S (?env i)"
      by (rule open_inst_regular[OF arg_exists])
    have env_closed: "\<And>i. dclosed0 S (?env i)"
      by (rule open_inst_dclosed0[OF zeroE arg_exists])
    have pms_fixed: "map (psubst ?env) pms = pms"
    proof (rule map_psubst_identity_wt[OF _ prefix])
      show "\<forall>i < length pms. \<exists>A. wt S D G (pms ! i) A"
        using ptyped by blast
    qed
    have lms_fixed: "map (psubst ?env) lms = lms"
    proof (rule map_psubst_identity_wt[OF _ prefix])
      show "\<forall>i < length lms.
          \<exists>A. wt S (insert 0 D) G (lms ! i) A"
        using ltyped by blast
    qed
    have args_fixed: "map (psubst ?env) ?oas = as"
      by (rule psubst_open_args[OF len])
    have oas_reg: "list_all (regular S) ?oas"
      by (auto simp: open_args_def list_all_iff)
    have elim_args_reg: "list_all (regular S)
        (elimArgs h C pms lms ?ss ?oas)"
      by (rule regular_elimArgs[
            OF plen llen pms_reg lms_reg oas_reg])

    have lm_typed: "wt S (insert 0 D) G (lms ! k)
        (methodTy h C ?ss)"
      using ltyped klm by simp
    have face0_typed: "wt S D G (dsubst S 0 D0 (lms ! k))
        (methodTy h C ?ss)"
    proof -
      have "wt S (dctx_subst 0 D0 (insert 0 D)) G
          (dsubst S 0 D0 (lms ! k)) (methodTy h C ?ss)"
        by (rule wt_dimension_subst[OF lm_typed wf])
      with zeroD show ?thesis
        by (simp add: dctx_subst_def)
    qed
    have face1_typed: "wt S D G (dsubst S 0 D1 (lms ! k))
        (methodTy h C ?ss)"
    proof -
      have "wt S (dctx_subst 0 D1 (insert 0 D)) G
          (dsubst S 0 D1 (lms ! k)) (methodTy h C ?ss)"
        by (rule wt_dimension_subst[OF lm_typed wf])
      with zeroD show ?thesis
        by (simp add: dctx_subst_def)
    qed
    have face0_head_reg: "regular S (dsubst S 0 D0 (lms ! k))"
      by (rule regular_wt[OF face0_typed])
    have face1_head_reg: "regular S (dsubst S 0 D1 (lms ! k))"
      by (rule regular_wt[OF face1_typed])
    have face0_reg: "regular S (open_face S G h C pms lms k D0)"
      unfolding open_face_def
      by (rule regular_apps[OF face0_head_reg elim_args_reg])
    have face1_reg: "regular S (open_face S G h C pms lms k D1)"
      unfolding open_face_def
      by (rule regular_apps[OF face1_head_reg elim_args_reg])

    have lhs_ep: "wf_endpt S h ?ss
        (fst (lends (S h) ! k)) (Hit h)"
      by (rule wf_hsig_lhs[OF sig k])
    have rhs_ep: "wf_endpt S h ?ss
        (snd (lends (S h) ! k)) (Hit h)"
      by (rule wf_hsig_rhs[OF sig k])
    have lhs_reg: "regular S
        (open_endpoint S G h C pms lms k
          (fst (lends (S h) ! k)))"
      unfolding open_endpoint_def
      by (rule regular_elimEnd[
            OF lhs_ep open_args_length oas_reg
              plen llen pms_reg lms_reg])
    have rhs_reg: "regular S
        (open_endpoint S G h C pms lms k
          (snd (lends (S h) ! k)))"
      unfolding open_endpoint_def
      by (rule regular_elimEnd[
            OF rhs_ep open_args_length oas_reg
              plen llen pms_reg lms_reg])

    have face0_head_fixed:
        "psubst ?env (dsubst S 0 D0 (lms ! k)) =
          dsubst S 0 D0 (lms ! k)"
      by (rule psubst_identity_wt[OF face0_typed prefix])
    have face1_head_fixed:
        "psubst ?env (dsubst S 0 D1 (lms ! k)) =
          dsubst S 0 D1 (lms ! k)"
      by (rule psubst_identity_wt[OF face1_typed prefix])
    have face0_inst:
        "psubst ?env (open_face S G h C pms lms k D0) =
          apps (dsubst S 0 D0 (lms ! k))
            (elimArgs h C pms lms ?ss as)"
      unfolding open_face_def
      by (simp add: psubst_elimArgs pms_fixed lms_fixed
          args_fixed face0_head_fixed)
    have face1_inst:
        "psubst ?env (open_face S G h C pms lms k D1) =
          apps (dsubst S 0 D1 (lms ! k))
            (elimArgs h C pms lms ?ss as)"
      unfolding open_face_def
      by (simp add: psubst_elimArgs pms_fixed lms_fixed
          args_fixed face1_head_fixed)
    have lhs_inst:
        "psubst ?env
          (open_endpoint S G h C pms lms k
            (fst (lends (S h) ! k))) =
          elimEnd S h C pms lms as (fst (lends (S h) ! k))"
      unfolding open_endpoint_def
      using psubst_elimEnd[OF lhs_ep open_args_length plen,
          where s = ?env]
      by (simp add: pms_fixed lms_fixed args_fixed)
    have rhs_inst:
        "psubst ?env
          (open_endpoint S G h C pms lms k
            (snd (lends (S h) ! k))) =
          elimEnd S h C pms lms as (snd (lends (S h) ! k))"
      unfolding open_endpoint_def
      using psubst_elimEnd[OF rhs_ep open_args_length plen,
          where s = ?env]
      by (simp add: pms_fixed lms_fixed args_fixed)

    have open0: "joinable S
        (open_face S G h C pms lms k D0)
        (open_endpoint S G h C pms lms k
          (fst (lends (S h) ! k)))"
      using open_obligations k by blast
    have open1: "joinable S
        (open_face S G h C pms lms k D1)
        (open_endpoint S G h C pms lms k
          (snd (lends (S h) ! k)))"
      using open_obligations k by blast
    have inst0: "joinable S
        (psubst ?env (open_face S G h C pms lms k D0))
        (psubst ?env
          (open_endpoint S G h C pms lms k
            (fst (lends (S h) ! k))))"
      by (rule joinable_psubst_dclosed[
            OF open0 face0_reg lhs_reg env_reg env_closed])
    have inst1: "joinable S
        (psubst ?env (open_face S G h C pms lms k D1))
        (psubst ?env
          (open_endpoint S G h C pms lms k
            (snd (lends (S h) ! k))))"
      by (rule joinable_psubst_dclosed[
            OF open1 face1_reg rhs_reg env_reg env_closed])
      show "joinable S
        (apps (dsubst S 0 D0 (lms ! k))
          (elimArgs h C pms lms ?ss as))
        (elimEnd S h C pms lms as
          (fst (lends (S h) ! k))) \<and>
      joinable S
        (apps (dsubst S 0 D1 (lms ! k))
          (elimArgs h C pms lms ?ss as))
        (elimEnd S h C pms lms as
          (snd (lends (S h) ! k)))"
        using inst0 inst1 face0_inst face1_inst lhs_inst rhs_inst
        by simp
    qed
  qed
qed

corollary normal_boundary_check_sound:
  assumes "normal_boundary_check S D G h C pms lms"
  shows "typed_coherent_methods S h C pms lms"
  by (rule open_boundary_check_sound)
    (use assms normal_boundary_check_iff_open_boundary_check in blast)

corollary open_boundary_square:
  assumes sig: "wf_hsig S h"
    and check: "open_boundary_check S D G h C pms lms"
    and k: "k < length (lcons (S h))"
    and len: "length as = length (lcons (S h) ! k)"
    and zero: "0 \<notin> E"
    and args: "\<forall>i < length as.
      wt S E H (as ! i) (argTy h (lcons (S h) ! k ! i))"
  shows "conv S
      (HElim h C pms lms (mkL S h k as D0))
      (apps (dsubst S 0 D0 (lms ! k))
        (elimArgs h C pms lms (lcons (S h) ! k) as))"
    and "conv S
      (HElim h C pms lms (mkL S h k as D1))
      (apps (dsubst S 0 D1 (lms ! k))
        (elimArgs h C pms lms (lcons (S h) ! k) as))"
  by (rule typed_elim_path_boundary_square[
        OF sig open_boundary_check_sound[OF check] k len zero args])+

end
