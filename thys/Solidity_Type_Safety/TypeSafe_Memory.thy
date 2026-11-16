section \<open>Type consistency for memory\<close>
theory TypeSafe_Memory
  imports TypeSafe_Base_Types
begin

fun extractType :: "mtypes \<Rightarrow> mtypes option" where
  "extractType (MTArray len arr) = Some arr"
| "extractType (MTValue v) = None"

definition AllocatedMem_between :: "memoryT \<Rightarrow> memoryT \<Rightarrow> location set"
  where
    "AllocatedMem_between st st' = ({ShowL\<^sub>n\<^sub>a\<^sub>t l | l. Toploc st \<le> l \<and> l < Toploc st'})
                                  \<union> fset(fmdom (Mapping (st')) - fmdom (Mapping (st)))"

primrec CompMemJustType::"mtypes \<Rightarrow> mtypes \<Rightarrow> bool"
  where
    "CompMemJustType (MTValue typ) mem = (mem = MTValue typ)"
  | "CompMemJustType (MTArray len arr) mem = (mem = (MTArray len arr) \<or> CompMemJustType arr mem)"

primrec CompMemType :: "memoryT \<Rightarrow> nat \<Rightarrow> mtypes \<Rightarrow> mtypes \<Rightarrow> location \<Rightarrow> location \<Rightarrow> bool"
  where
    "CompMemType mem len (MTValue typ) childtp parentloc childloc = (childtp = (MTValue typ) \<and> (\<exists>i<len. (hash parentloc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) = childloc))"
  | "CompMemType mem len (MTArray len' arr) childtp parentloc childloc = (\<exists>i<len. \<exists>l. accessStore (hash parentloc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l) \<and>
                                                                          ((l = childloc \<and> (MTArray len' arr) = childtp) \<or> CompMemType mem len' arr childtp l childloc)
                                                                        )"

text \<open>All memory locations occupied by a value of the given memory type, starting
  at a base location and following array pointers in the given memory.\<close>

fun GetAllMemoryLocations :: "mtypes \<Rightarrow> location \<Rightarrow> memoryT \<Rightarrow> location set"
  where
    "GetAllMemoryLocations (MTValue _) base_loc _ = {base_loc}"
  | "GetAllMemoryLocations (MTArray len struct) base_loc mem =
     (\<Union>i\<in>{0..<len}.
       (case accessStore (hash base_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem of
          Some (MPointer ptr) \<Rightarrow> {(hash base_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i))} \<union> GetAllMemoryLocations struct ptr mem
        | Some (MValue _) \<Rightarrow> {(hash base_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i))} \<union> GetAllMemoryLocations struct (hash base_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem
        | None \<Rightarrow> {}))"

subsection \<open>Memory and calldata conformity\<close>

text \<open>@{text MCon} checks that the sub-locations of a memory or calldata
  structure conform to their types. Starting at a location, it checks all
  sub-locations. For an array, every element is checked recursively; for a value
  type, the string stored at the location is checked against its base type.

  Locations stored in the @{const Denvalue} for memory references already denote
  the target of the pointer, following the convention of @{const expressions_with_gas.msel}. For
  example, if a memory array stored at \<open>0.0\<close> has pointer value \<open>7.7\<close>, the
  environment stores \<open>7.7\<close>. Hence @{text MCon} does not dereference its
  location argument.\<close>

primrec MCon :: "mtypes \<Rightarrow> memoryT \<Rightarrow> location \<Rightarrow> bool"
  where
    "MCon (MTValue typ) msto loc =(case (accessStore loc msto) of
                                  (Some (MValue t)) \<Rightarrow> (typeCon typ t)
                                    | (Some(MPointer t)) \<Rightarrow> False
                                    | None \<Rightarrow> False)"

|"MCon (MTArray len arr) msto loc = (len>0 \<and> (\<forall>i < len.
                                                (case (accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) msto) of
                                                 (Some (MPointer loc2)) \<Rightarrow>
                                                        (case arr of (MTArray len' arr') \<Rightarrow> (MCon arr msto (loc2))
                                                            | MTValue val \<Rightarrow> False)
                                                  | Some(MValue val) \<Rightarrow>
                                                    (case arr of (MTValue typ) \<Rightarrow> (MCon arr msto (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
                                                      | (MTArray l a) \<Rightarrow> False)
                                                  | None \<Rightarrow> False))
                                    \<and> (\<exists>p. accessStore loc msto = Some (MPointer p) \<or> accessStore loc msto = None))"

primrec MConAccessSame:: "location \<Rightarrow> location \<Rightarrow> mtypes \<Rightarrow> memoryT \<Rightarrow> memoryT \<Rightarrow> bool"
  where
    "MConAccessSame l1 l2 (MTValue t) m1 m2 = (\<exists>val. accessStore l1 m1 = Some (MValue val) \<and> (\<exists>val'. accessStore l2 m2 = Some (MValue val')))"
  | "MConAccessSame l1 l2 (MTArray len t) m1 m2 = (\<forall>i1<len. \<forall>i2<len. (\<forall>l. accessStore (hash l1 (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) m1 = Some (MPointer l) \<longrightarrow>
                                                                (\<exists>l'. accessStore (hash l2 (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) m2 = Some (MPointer l')
                                                                \<and> MConAccessSame l l' t m1 m2)))"
text \<open>The set of all memory locations reachable from the memory references of
  an environment and stack.\<close>

fun ReachableMem :: "environment \<Rightarrow> stack \<Rightarrow> memoryT \<Rightarrow> location set"
  where
    "ReachableMem env st mem = (\<Union> (t, l) \<in> fset(fmran (Denvalue env)).
         (case l of
           Stackloc loc \<Rightarrow>
             (case accessStore loc st of
               Some (KMemptr ptr) \<Rightarrow>
                 (case t of
                   type.Memory struct \<Rightarrow> GetAllMemoryLocations struct ptr mem
                    | _ \<Rightarrow> {})
               | _ \<Rightarrow> {})
            | Storeloc loc \<Rightarrow> {}))"


primrec TypedMemSubPref:: "location \<Rightarrow> location \<Rightarrow> mtypes \<Rightarrow> bool"
  where
    "TypedMemSubPref child parent (MTValue t) = (child = parent)"
  | "TypedMemSubPref child parent (MTArray len t) = (\<exists>i<len. TypedMemSubPref child (hash parent (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t
      \<or> child = (hash parent (ShowL\<^sub>n\<^sub>a\<^sub>t i)))"

primrec TypedMemSubPrefPtrs:: "memoryT \<Rightarrow> nat \<Rightarrow> mtypes\<Rightarrow> location \<Rightarrow> location \<Rightarrow> bool"
  where
    "TypedMemSubPrefPtrs mem len (MTValue t) parent child = (\<exists>i<len. (hash parent (ShowL\<^sub>n\<^sub>a\<^sub>t i)) = child)"
  | "TypedMemSubPrefPtrs mem len (MTArray len' t) parent child = (\<exists>i<len. \<exists>l. accessStore (hash parent (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l)
                                                                  \<and> (l = child \<or> TypedMemSubPrefPtrs mem len' t l child ))"

definition WrittenMem_between :: "memoryT \<Rightarrow> memoryT \<Rightarrow> location set"
  where
    "WrittenMem_between st st' = {l. accessStore l st \<noteq> accessStore l (st')}"

definition compMemPtrs :: "stack \<Rightarrow> memoryT \<Rightarrow> (String.literal, type \<times> denvalue) fmap \<Rightarrow> bool" where
  "compMemPtrs st mem denval = (\<forall>tp1 tp2 l1 l2 stl1 stl2 dloc1.
          (type.Memory tp1, Stackloc l1) |\<in>| fmran denval \<and> (type.Memory tp2, Stackloc l2) |\<in>| fmran denval
          \<and> accessStore l1 st = Some(KMemptr stl1) \<and> accessStore l2 st = Some(KMemptr stl2)
      \<longrightarrow> (if stl1 = stl2 then tp1 = tp2 else
            (case tp1 of
              MTValue val \<Rightarrow>
                (case tp2 of MTValue val2 \<Rightarrow> True
                  | MTArray len2 arr2 \<Rightarrow> (if TypedMemSubPrefPtrs mem len2 arr2 stl2 stl1 then CompMemType mem len2 arr2 (MTValue val) stl2 stl1
                                          else True))
             | MTArray len arr \<Rightarrow>
                (case tp2 of MTValue val2 \<Rightarrow> (if TypedMemSubPrefPtrs mem len arr stl1 stl2 then CompMemType mem len arr (MTValue val2) stl1 stl2
                                            else True)
                  | MTArray len2 arr2 \<Rightarrow> (if TypedMemSubPrefPtrs mem len2 arr2 stl2 stl1 then CompMemType mem len2 arr2 (MTArray len arr) stl2 stl1
                                          else if TypedMemSubPrefPtrs mem len arr stl1 stl2 then CompMemType mem len arr (MTArray len2 arr2) stl1 stl2
                                          else if (TypedMemSubPrefPtrs mem len arr stl1 dloc1 \<and> TypedMemSubPrefPtrs mem len2 arr2 stl2 dloc1)
                                                  then (\<exists>dt. CompMemType mem len2 arr2 dt stl2 dloc1
                                                                         \<and> CompMemType mem len arr dt stl1 dloc1
                                                                         )
                                          else True))

)))"

definition compMemPtrs3 :: "stack \<Rightarrow> memoryT \<Rightarrow> (String.literal, type \<times> denvalue) fmap \<Rightarrow> bool" where
  "compMemPtrs3 st mem denval = (\<forall>tp1 tp2 l1 l2 stl1 stl2 dloc1.
    (type.Memory tp1, Stackloc l1) |\<in>| fmran denval \<and> (type.Memory tp2, Stackloc l2) |\<in>| fmran denval
    \<and> accessStore l1 st = Some(KMemptr stl1) \<and> accessStore l2 st = Some(KMemptr stl2)
    \<longrightarrow> (if stl1 = stl2 then tp1 = tp2 else
      (case (tp1, tp2) of
          (MTValue val, MTValue val2) \<Rightarrow> True
        | (MTValue val, MTArray len2 arr2) \<Rightarrow> \<not> (TypedMemSubPrefPtrs mem len2 arr2 stl2 stl1) \<or> CompMemType mem len2 arr2 (MTValue val) stl2 stl1
        | (MTArray len arr, MTValue val2) \<Rightarrow> \<not> (TypedMemSubPrefPtrs mem len arr stl1 stl2) \<or> CompMemType mem len arr (MTValue val2) stl1 stl2
        | (MTArray len arr, MTArray len2 arr2) \<Rightarrow>
            if (TypedMemSubPrefPtrs mem len arr stl1 dloc1 \<and> TypedMemSubPrefPtrs mem len2 arr2 stl2 dloc1)
                then (\<exists>dt. CompMemType mem len2 arr2 dt stl2 dloc1 \<and> CompMemType mem len arr dt stl1 dloc1 )
            else True)
      )
    )"


fun mtype_size :: "mtypes \<Rightarrow> nat" where
  "mtype_size (MTValue _) = 1"
| "mtype_size (MTArray _ S) = 1 + mtype_size S"

subsection \<open>Type relations between arrays and their elements\<close>

lemma CompMemJustTypes_trns:
  assumes "CompMemJustType tp1 tp2"
    and "CompMemJustType tp1 tp3"
  shows "CompMemJustType tp2 tp3 \<or> CompMemJustType tp3 tp2" using assms
proof(induction tp1 arbitrary:tp2 tp3)
  case (MTArray x1 tp1)
  then show ?case by auto
next
  case (MTValue x)
  then show ?case by simp
qed

lemma CompMemType_SameAccessAllocate:
  assumes "\<forall>loc. accessStore loc m = accessStore loc (snd (allocate m'))"
    and "CompMemType m len t1 t2 l1 l2"
  shows "CompMemType m' len t1 t2 l1 l2" using assms
proof(induction t1 arbitrary:len l1)
  case (MTArray x1 t1)
  then obtain i l where idef:"i<len \<and> accessStore (hash l1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some (MPointer l)
                              \<and> (l = l2 \<and> MTArray x1 t1 = t2 \<or> CompMemType m x1 t1 t2 l l2)"
    unfolding CompMemType.simps by auto
  then show ?case
  proof(cases "l = l2")
    case True
    then show ?thesis using idef MTArray.prems
      by (metis (no_types, lifting) CompMemType.simps(2) MTArray.IH allocateSameAccess)
  next
    case False
    then show ?thesis using idef MTArray
      by (metis CompMemType.simps(2) allocateSameAccess)
  qed
next
  case (MTValue x)
  then show ?case by auto
qed

lemma CompMemType_imps_CompMemJustType:
  assumes "CompMemType mem len t1 t2 l1 l2"
  shows "CompMemJustType (MTArray len t1) t2" using assms
proof(induction t1 arbitrary:l1 len)
  case (MTArray x1 t2')
  then show ?case
  proof(cases "t2 = MTArray x1 t2'")
    case True
    then show ?thesis by simp
  next
    case False
    then have a10:"(\<exists>i<len. \<exists>l. accessStore (hash l1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l) \<and> (l =
        l2 \<and> MTArray x1 t2' = t2 \<or> CompMemType mem x1 t2' t2 l l2))"
      using MTArray(2) CompMemType.simps(2)[of mem len x1 t2' t2 l1 l2] by simp

    have "CompMemJustType t2' t2"
      using False MTArray.IH a10 by auto
    then show ?thesis using False by simp
  qed
next
  case (MTValue x)
  then show ?case using CompMemJustType.simps(1) CompMemType.simps(1) by simp
qed

lemma CompMemType_imps_TypedMemSubPrefPtrs:
  assumes "CompMemType mem len tp tc lp lc"
  shows "TypedMemSubPrefPtrs mem len tp lp lc" using assms
proof(induction tp arbitrary:lp len)
  case (MTArray x1 tp)
  then show ?case
    using MTArray.IH by auto
next
  case (MTValue x)
  then show ?case by simp
qed

lemma CompMemTypes_asc:
  assumes "CompMemJustType tp1 tp2"
    and "CompMemJustType tp2 tp3"
  shows "CompMemJustType tp1 tp3" using assms
proof(induction tp1)
  case (MTArray x1 tp1)
  then show ?case by auto
next
  case (MTValue x)
  then show ?case by simp
qed

lemma MConArrayPointers:
  assumes "MCon (MTArray len (MTArray len' t)) v' loc"
    and "len >0"
    and "i < len"
  obtains val where "accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = Some (MPointer val)"
proof -
  have a10:"\<forall>i<len.
             case accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' of None \<Rightarrow> False
             | Some (MValue val) \<Rightarrow>
                 (case MTArray len' t of MTValue typ \<Rightarrow> MCon (MTArray len' t) v' (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i))
                  | _ \<Rightarrow> False)
             | Some (MPointer loc2) \<Rightarrow>
                 (case MTArray len' t of MTArray len'a arr' \<Rightarrow> MCon (MTArray len' t) v' loc2
                 | MTValue Types \<Rightarrow> False)"
    using MCon.simps(2)[of len "MTArray len' t" v' loc] assms(1) by simp
  show ?thesis
  proof(cases "accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'")
    case None
    then show ?thesis using a10 assms by auto
  next
    case (Some a)
    then show ?thesis
    proof(cases a)
      case (MValue x1)
      then show ?thesis using a10 assms Some by auto
    next
      case MPointer
      then show ?thesis using Some that by auto
    qed
  qed
qed


lemma MCon_array_decrement:
  assumes "MCon (MTArray len t) v' loc"
    and "len -1 > 0"
  shows "MCon (MTArray (len-1) t) v' loc" using assms MCon.simps by simp

lemma MConTypeSplitingArray:
  assumes "\<forall>(i::nat)<(x1::nat).
             (case accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem of
                Some (MPointer loc2) =>
                    (case tp1 of MTArray len' arr' => MCon tp1 mem loc2
                               | MTValue tps => False)
              | Some (MValue val) =>
                    (case tp1 of (MTArray n mt) => False
                                | MTValue tps => MCon tp1 mem (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
              | None => False)"
    and "\<exists>a b. tp1 = MTArray a b"
    and "(i::nat)<x1"
  shows "\<exists>p. accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer p)"
proof(cases "accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem")
  case None
  then show ?thesis using assms(1) assms(3) by auto
next
  case (Some a)
  then show ?thesis
  proof(cases a)
    case (MValue x1)
    then show ?thesis using assms Some by auto
  next
    case (MPointer x2)
    then show ?thesis using assms Some by auto
  qed
qed

lemma MConSubTypes:
  assumes "MCon (MTArray len t') mem loc"
  shows "\<forall>t. CompMemJustType t' t \<longrightarrow> (\<not>MCon t mem loc)" using assms
proof(induction t' arbitrary: len loc)
  case (MTArray x1 t')
  show ?case
  proof intros
    fix t
    assume *:"CompMemJustType (MTArray x1 t') t"
    then have a5:"t = MTArray x1 t' \<or> CompMemJustType t' t" by (cases t) auto

    have a10:" \<forall>i<len.
             case accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem of None \<Rightarrow> False
             | Some (MValue val) \<Rightarrow> (case MTArray x1 t' of MTArray n mtypes \<Rightarrow> False
                                        | MTValue typ \<Rightarrow> MCon (MTArray x1 t') mem (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
             | Some (MPointer loc2) \<Rightarrow> (case MTArray x1 t' of MTArray len' arr' \<Rightarrow> MCon (MTArray x1 t') mem loc2
                                        | MTValue Types \<Rightarrow> False)"
      using MTArray(2) MCon.simps(2)[of len "MTArray x1 t'" mem loc] by simp
    then obtain p' i where p'def:" i<len \<and> accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer p')"
      by (metis MConArrayPointers MTArray.prems(1) MCon.simps(2))
    then have a20:"MCon (MTArray x1 t') mem p'" using a10 by fastforce
    then have a30:"\<forall>t. CompMemJustType t' t \<longrightarrow> \<not> MCon t mem p'" using MTArray.IH by auto

    then show "\<not> MCon t mem loc"
    proof(cases "t = MTArray x1 t'")
      case True
      show ?thesis
      proof
        assume ***:"MCon t mem loc"
        then have a90:"\<forall>i<x1.
             (case accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem of None \<Rightarrow> False
                  | Some (MValue val) \<Rightarrow> (case t' of MTArray n mtypes \<Rightarrow> False | MTValue typ \<Rightarrow> MCon t' mem (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
              | Some (MPointer loc2) \<Rightarrow> (case t' of MTArray len' arr' \<Rightarrow> MCon t' mem loc2 | MTValue Types \<Rightarrow> False))"
          using MCon.simps(2)[of x1 t' mem loc ] using True by auto
        then obtain i' where i'Def:"i'<x1 \<and> i' <len"
          using "*" MTArray.prems \<open>MCon t mem loc\<close>
          using True by fastforce
        then obtain p'' where p''def: "accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i')) mem = Some (MPointer p'')" using a10 p'def
            MConTypeSplitingArray[of len "MTArray x1 t'" mem loc i'] by auto
        then have "MCon t' mem p''" using a90 i'Def
          by (metis (no_types, lifting) mtypes.exhaust mtypes.simps(5) mtypes.simps(6) memoryvalue.simps(6) Option.option.simps(5))
        moreover have "MCon (MTArray x1 t') mem p''" using p''def i'Def a10 by auto
        ultimately show False using a20
          using "*" MTArray.prems \<open>MCon t mem loc\<close>
          by (metis MTArray.IH CompMemJustType.simps(1) CompMemJustType.simps(2) extractType.elims)
      qed
    next
      case False
      then have "CompMemJustType t' t" using a5 by auto
      then have "\<not> MCon t mem p'" using a30 by auto
      show ?thesis
      proof
        assume ***:"MCon t mem loc"
        then show False
        proof(cases t)
          case mta:(MTArray x11 x12)
          then have c10:"\<forall>i<x11.
             (case accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem of None \<Rightarrow> False
              | Some (MValue val) \<Rightarrow> (case x12 of MTArray n mtypes \<Rightarrow> False | MTValue typ \<Rightarrow> MCon x12 mem (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
              | Some (MPointer loc2) \<Rightarrow> (case x12 of MTArray len' arr' \<Rightarrow> MCon x12 mem loc2 | MTValue Types \<Rightarrow> False))"
            using *** MCon.simps(2)[of x11 x12 mem loc] by simp
          then obtain i''' where i'''def:"i'''<x11 \<and> i'''<len"
            by (metis "***" mta MTArray.prems neq0_conv MCon.simps(2))
          then obtain p'' where p''def: "accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i''')) mem = Some (MPointer p'')"
            using a10 p'def MConTypeSplitingArray[of len "MTArray x1 t'" mem loc i'''] by auto
          then have "MCon (MTArray x1 t') mem p''" using a10 i'''def by fastforce
          have "MCon x12 mem p''" using i'''def p''def c10 mta
            by (metis (no_types, lifting) mtypes.exhaust mtypes.simps(5) mtypes.simps(6) memoryvalue.simps(6) Option.option.simps(5))
          then show ?thesis using MCon.simps(2)[of x11 x12 mem loc]
            by (metis CompMemTypes_asc MTArray.IH \<open>CompMemJustType t' t\<close> \<open>MCon (MTArray x1 t') mem p''\<close> mta
                CompMemJustType.simps(1) CompMemJustType.simps(2) extractType.cases)
        next
          case (MTValue x2)
          then show ?thesis using p'def *** MCon.simps(1)[of x2 mem loc]
            using MTArray.prems by force
        qed

      qed
    qed
  qed
next
  case (MTValue x)
  show ?case
  proof intros
    fix t
    assume *:"CompMemJustType (MTValue x) t "
    then have **:"t = MTValue x" by simp
    moreover have "\<forall>i<len.
             case accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem of None \<Rightarrow> False
             | Some (MValue val) \<Rightarrow> (case MTValue x of MTArray n mtypes \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTValue x) mem (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
             | Some (MPointer loc2) \<Rightarrow> (case MTValue x of MTArray len' arr' \<Rightarrow> MCon (MTValue x) mem loc2 | MTValue Types \<Rightarrow> False)"
      using MTValue MCon.simps(2)[of len "MTValue x" mem loc] by auto
    then show "\<not> MCon t mem loc" using MTValue **
      by (metis memoryvalue.simps(6) Option.option.simps(4) Option.option.simps(5) MCon.simps(1) MCon.simps(2))
  qed
qed

lemma MConPtrsMustBeSubLocs:
  assumes "MCon (MTArray len t') mem loc"
  shows "\<forall>p i. i<len \<and> accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer p) \<longrightarrow> p \<noteq> loc"
proof intros
  fix i p
  assume *:"i < len \<and> accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer p)"
  then have a10:"(case t' of MTArray len' arr' \<Rightarrow> MCon t' mem p | MTValue Types \<Rightarrow> False)"
    using assms MCon.simps(2)[of len t' mem loc] by auto
  then have "MCon t' mem p" using * by (cases t'; simp)
  then show "p\<noteq>loc" using assms MConSubTypes[of len t' mem loc]
    by (metis CompMemJustType.simps(1) CompMemJustType.simps(2) extractType.cases)
qed

lemma MConPtrsMustBeSubLocs_CompMemType:
  assumes "MCon (MTArray len arr) mem loc"
  shows "\<forall>p t. MCon t mem p \<and> CompMemType mem len arr t loc p \<longrightarrow> p \<noteq> loc" using assms
proof (induction arr arbitrary:len loc)
  case (MTArray x1 arr)
  show ?case
  proof(intros)
    fix p t
    assume *:"MCon t mem p \<and> CompMemType mem len (MTArray x1 arr) t loc p"

    show "p \<noteq> loc"
    proof
      assume **:"p = loc"
      have "(\<exists>i<len. \<exists>l. accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l)
            \<and> (l = p \<and> MTArray x1 arr = t \<or> CompMemType mem x1 arr t l p))"
        using * CompMemType.simps(2)[of mem len x1 arr t loc p] by auto
      then obtain i l where idef:"i<len \<and> accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l)
                                  \<and> (l = p \<and> MTArray x1 arr = t \<or> CompMemType mem x1 arr t l p)" by blast
      then have "(case accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem of None \<Rightarrow> False
              | Some (MValue val) \<Rightarrow> (case MTArray x1 arr of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon
                  (MTArray x1 arr) mem (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
              | Some (MPointer loc2) \<Rightarrow> (case MTArray x1 arr of MTArray len' arr' \<Rightarrow> MCon (MTArray x1 arr) mem loc2 | MTValue Types \<Rightarrow> False))
            \<and> ((\<exists>p. accessStore loc mem = Some (MPointer p)) \<or> accessStore loc mem = None)"
        using MTArray(2) MCon.simps(2)[of len "MTArray x1 arr" mem loc] by metis
      then have "MCon (MTArray x1 arr) mem l" using idef by force
      show False
      proof(cases "l = p \<and> MTArray x1 arr = t")
        case True
        then show ?thesis
          using "**" idef
          using MConPtrsMustBeSubLocs MTArray.prems by blast
      next
        case False
        then have "CompMemType mem x1 arr t l p" using idef by auto
        then have "p \<noteq> l"
          using "**" MConPtrsMustBeSubLocs MTArray.prems MConSubTypes[of len "(MTArray x1 arr)" mem loc]
          using idef by blast
        then show ?thesis
          using "*" "**" CompMemType_imps_CompMemJustType MConSubTypes MTArray.prems \<open>CompMemType mem x1 arr t l p\<close> by blast
      qed
    qed
  qed
next
  case (MTValue x)
  then show ?case by fastforce
qed


lemma BothMConImpsNotCompMemType:
  assumes "MCon (MTArray len arr) mem p''"
    and "MCon t' mem p''"
  shows "\<not>CompMemType mem len arr t' p'' p''" using assms
proof(induction arr arbitrary:len p'')
  case (MTArray x1 arr)
  then show ?case
    by (meson MConPtrsMustBeSubLocs_CompMemType)
next
  case (MTValue x)
  then show ?case by fastforce
qed

lemma MCon_imps_Some:
  assumes "MCon t' mem p'"
  shows "\<exists>x i. accessStore p' mem = Some x \<or> accessStore (hash p' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some x"
proof(cases t')
  case (MTArray x11 x12)
  then have a10:"\<forall>i<x11.
             (case accessStore (hash p' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem of None \<Rightarrow> False
              | Some (MValue val) \<Rightarrow> (case x12 of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon x12 mem (hash p' (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
              | Some (MPointer loc2) \<Rightarrow> (case x12 of MTArray len' arr' \<Rightarrow> MCon x12 mem loc2 | MTValue Types \<Rightarrow> False))"
    using assms MCon.simps(2)[of x11 x12 "mem" p'] by simp
  then obtain i where a20:"i<x11 "
    using MTArray assms by fastforce
  then show ?thesis
  proof(cases " accessStore (hash p' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem")
    case None
    then show ?thesis using a10 a20 by auto
  next
    case (Some a)
    then show ?thesis
      by auto
  qed
next
  case (MTValue x2)
  then have a10:"(case accessStore p' mem of None \<Rightarrow> False | Some (MValue t) \<Rightarrow> typeCon x2 t | Some (MPointer t) \<Rightarrow> False)"
    using assms(1) MCon.simps(1)[of x2 "mem" p'] by auto
  then show ?thesis
  proof(cases "accessStore p' mem")
    case None
    then show ?thesis using a10 by simp
  next
    case (Some a)
    then show ?thesis by auto
  qed
qed

lemma MCon_subTypes_imps_noPrnt:
  assumes "MCon (MTArray x t) mem l"
    and "MCon (MTArray x' (MTArray x t)) mem l'"
  shows "\<not>CompMemType mem x t (MTArray x' (MTArray x t)) l l'" using assms
  using CompMemType_imps_CompMemJustType MConSubTypes by blast

abbreviation example_mem_array_bool::memoryT
  where "example_mem_array_bool \<equiv>
    \<lparr>Mapping = fmap_of_list
      [(STR ''1.1.0'', MValue STR ''False''),
       (STR ''0.1.0'', MValue STR ''True''),
       (STR ''1.0'', MPointer STR ''1.0''),
       (STR ''1.0.0'', MValue STR ''False''),
       (STR ''0.0.0'', MValue STR ''True''),
       (STR ''0.0'', MPointer STR ''0.0'')],
     Toploc = 1,
     Typed_Mapping = fmap_of_list
      [(STR ''1.1.0'', MTValue TBool),
       (STR ''0.1.0'', MTValue TBool),
       (STR ''1.0'', MTArray 2 (MTValue TBool)),
       (STR ''1.0.0'', MTValue TBool),
       (STR ''0.0.0'', MTValue TBool),
       (STR ''0.0'', MTArray 2 (MTValue TBool))]\<rparr>"

lemma MCon_sub_MTVal_imps_val:
  assumes "MCon (MTArray len (MTValue t)) mm loc"
  shows "\<forall>i<len. \<exists>val. accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mm = Some (MValue val)"
proof intros
  fix i
  assume "i<len"
  then have a10:"case accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mm of None \<Rightarrow> False
             | Some (MValue val) \<Rightarrow> (case MTValue t of MTArray n mtypes \<Rightarrow> False
                                        | MTValue typ \<Rightarrow> MCon (MTValue t) mm (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
             | Some (MPointer loc2) \<Rightarrow> (case MTValue t of MTArray len' arr' \<Rightarrow> MCon (MTValue t) mm loc2
                                          | MTValue Types \<Rightarrow> False)"
    using assms(1) MCon.simps(2)[of len "MTValue t" mm loc] by simp
  show "\<exists>val. accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mm = Some (MValue val) "
  proof(cases "accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mm")
    case None
    then show ?thesis using a10 by simp
  next
    case (Some a)
    then show ?thesis
    proof(cases a)
      case (MValue x1)
      then show ?thesis using a10 Some by auto
    next
      case (MPointer x2)
      then show ?thesis using a10 Some by auto
    qed
  qed
qed

lemma CompTypeRemainsMCon:
  assumes "CompMemType mem len arr t2 p' stl1"
    and "MCon (MTArray len arr) mem p'"
  shows "MCon t2 mem stl1" using assms
proof(induction arr arbitrary: len p')
  case (MTArray x1 arr)
  then have a10:"\<forall>i<len.
             (case accessStore (hash p' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem of
               Some (MPointer loc2) \<Rightarrow> MCon (MTArray x1 arr) mem loc2) \<and>
             ((\<exists>p. accessStore p' mem = Some (MPointer p)) \<or> accessStore p' mem = None)"
    using MCon.simps(2)[of len "MTArray x1 arr" mem p']
    by (metis MConArrayPointers mtypes.simps(5) memoryvalue.simps(6) Option.option.simps(5))
  have "(\<exists>i<len. \<exists>l. accessStore (hash p' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l)
        \<and> (l = stl1 \<and> MTArray x1 arr = t2 \<or> CompMemType mem x1 arr t2 l stl1))"
    using MTArray CompMemType.simps(2)[of mem len x1 arr t2 p' stl1] by auto
  then obtain i l where idef:"i<len \<and> accessStore (hash p' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l)
        \<and> (l = stl1 \<and> MTArray x1 arr = t2 \<or> CompMemType mem x1 arr t2 l stl1)" by blast
  then show ?case
  proof(cases "l = stl1 \<and> MTArray x1 arr = t2")
    case True
    then show ?thesis using a10 idef by auto
  next
    case False
    then show ?thesis using MTArray.IH[of x1 l] a10 idef by fastforce
  qed
next
  case (MTValue x)
  then have a10:"\<forall>i<len.
             (case accessStore (hash p' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem of None \<Rightarrow> False
              | Some (MValue val) \<Rightarrow> (case MTValue x of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTValue x) mem (hash p' (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
              | Some (MPointer loc2) \<Rightarrow> (case MTValue x of MTArray len' arr' \<Rightarrow> MCon (MTValue x) mem loc2 | MTValue Types \<Rightarrow> False)) \<and>
             ((\<exists>p. accessStore p' mem = Some (MPointer p)) \<or> accessStore p' mem = None)"
    using MCon.simps(2)[of len "MTValue x" mem p'] by simp
  have a20:"(t2 = MTValue x \<and> (\<exists>i<len. hash p' (ShowL\<^sub>n\<^sub>a\<^sub>t i) = stl1))" using MTValue CompMemType.simps(1)[of mem len x t2 p' stl1] by auto
  then obtain i where idef:"i<len \<and> hash p' (ShowL\<^sub>n\<^sub>a\<^sub>t i) = stl1" by auto
  then have "MCon (MTValue x) mem (hash p' (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using a10
    by (metis MCon_sub_MTVal_imps_val MTValue.prems(2) mtypes.simps(6) memoryvalue.simps(5) Option.option.simps(5))
  then show ?case using idef a20 by auto
qed

lemma CompMemJustType_refl: "CompMemJustType t t"
  by (cases t) simp_all

text \<open>Two sub-types of a common type that are both consistent at the same
  location are equal.\<close>

lemma MCon_CompMemJustType_unique:
  assumes "CompMemJustType t t1" and "CompMemJustType t t2"
    and "MCon t1 mem l" and "MCon t2 mem l"
  shows "t1 = t2"
proof -
  from CompMemJustTypes_trns[OF assms(1,2)]
  consider "CompMemJustType t1 t2" | "CompMemJustType t2 t1" by blast
  then show ?thesis
  proof cases
    case 1
    show ?thesis
    proof (cases t1)
      case (MTValue v)
      then show ?thesis using 1 by simp
    next
      case (MTArray n a)
      then show ?thesis using 1 assms(3,4) MConSubTypes[of n a mem l] by auto
    qed
  next
    case 2
    show ?thesis
    proof (cases t2)
      case (MTValue v)
      then show ?thesis using 2 by simp
    next
      case (MTArray n a)
      then show ?thesis using 2 assms(3,4) MConSubTypes[of n a mem l] by auto
    qed
  qed
qed


subsection \<open>Consistency under memory changes\<close>

lemma GetAllMemoryLocations_Arry_Contains_Indexs:
  assumes "MCon (MTArray len2 arr2) mem stl2"
  shows "\<forall>i<len2. hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<in> GetAllMemoryLocations (MTArray len2 arr2) stl2 mem" using assms
proof(cases arr2)
  case (MTArray x1 arr2')
  show ?thesis
  proof intros
    fix i
    assume *:"i<len2"
    then have "\<exists>c. accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer c)"
      using assms MTArray by (metis MConArrayPointers not_gr0 not_less0)
    then show "hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<in> GetAllMemoryLocations (MTArray len2 arr2) stl2 mem"
      unfolding GetAllMemoryLocations.simps using * by fastforce
  qed
next
  case (MTValue x)
  have exp:"GetAllMemoryLocations (MTArray len2 (MTValue x)) stl2 mem = (\<Union>i\<in>{0..<len2}.
        case accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem of None \<Rightarrow> {} | Some (MValue xa) \<Rightarrow> {hash
            stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)} \<union> {hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)} | Some (MPointer ptr)
            \<Rightarrow> {hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)} \<union> {ptr})"
    unfolding GetAllMemoryLocations.simps by blast
  show ?thesis
  proof intros
    fix i assume *:"i<len2"
    then have "i \<in> {0..<len2}" by simp
    then have exp':"(case accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem of None \<Rightarrow> {} | Some (MValue xa)
        \<Rightarrow> {hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)} \<union> {hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)} | Some (MPointer
        ptr) \<Rightarrow> {hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)} \<union> {ptr})
\<subseteq> GetAllMemoryLocations (MTArray len2 (MTValue x)) stl2 mem" using exp by blast
    have "\<exists>c. accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MValue c)" using MTValue assms *
      using MCon_sub_MTVal_imps_val by blast
    then have "(case accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem of None \<Rightarrow> {} | Some (MValue xa) \<Rightarrow>
        {hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)} \<union> {hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)} | Some (MPointer ptr)
        \<Rightarrow> {hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)} \<union> {ptr})
                    = {hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)}" by auto
    then have "{hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)} \<subseteq> GetAllMemoryLocations (MTArray len2 (MTValue x)) stl2 mem" using exp' by simp
    then show "hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<in> GetAllMemoryLocations (MTArray len2 arr2) stl2 mem" using MTValue by blast
  qed
qed

lemma MCon_imps_sub_Mcon:
  assumes "MCon (MTArray arLen t) srcMem srcl"
  shows "\<forall>x::nat<arLen. (\<forall>l. accessStore (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) srcMem = Some (MPointer l) \<longrightarrow> MCon t srcMem l)
      \<and> (\<forall>val. accessStore (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) srcMem = Some (MValue val) \<longrightarrow> MCon t srcMem (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)))"
  using assms
proof(induction t arbitrary: arLen srcl)
  case (MTArray x1 t)
  show ?case
  proof(intros)
    fix x l
    assume *:"x<arLen"
      and "accessStore (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) srcMem = Some (MPointer l)"
    then show "MCon (MTArray x1 t) srcMem l" using MTArray
      by (meson CompTypeRemainsMCon CompMemType.simps(2))
  next
    fix x val
    assume *:"x<arLen"
      and "accessStore (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) srcMem = Some (MValue val)"
    then show "MCon (MTArray x1 t) srcMem (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t x))" using MTArray by auto
  qed
next
  case (MTValue x)
  show ?case
  proof(intros)
    fix xa l
    assume *:"xa<arLen"
      and **:"accessStore (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t xa)) srcMem = Some (MPointer l)"
    show "MCon (MTValue x) srcMem l" using * **
      using MTValue by force
  next
    fix xa val
    assume *:"xa<arLen"
      and **:"accessStore (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t xa)) srcMem = Some (MValue val)"
    show "MCon (MTValue x) srcMem (hash srcl (ShowL\<^sub>n\<^sub>a\<^sub>t xa))" using * ** MTValue by auto
  qed
qed

lemma MconSameTypeSameAccessWithTyping:
  assumes "MCon (MTArray x t) m1 l1"
    and "MCon (MTArray x t) m2 l2"
  shows "\<forall>i1<x. \<forall>i2<x. (\<forall>l. accessStore (hash l1 (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) m1 = Some (MPointer l)
      \<longrightarrow> (\<exists>l'. accessStore (hash l2 (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) m2 = Some (MPointer l') \<and> MCon t m1 l
      \<and> MCon t m2 l'))
        \<and> (\<forall>val . accessStore (hash l1 (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) m1 = Some (MValue val) \<longrightarrow>
            (\<exists>val'. accessStore (hash l2 (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) m2 = Some (MValue val')\<and> MCon t m1 (hash l1
            (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) \<and> MCon t m2 (hash l2 (ShowL\<^sub>n\<^sub>a\<^sub>t i2))))"
  using assms
proof(induction t arbitrary:x l1 l2)
  case (MTArray x1 t)
  show ?case
  proof(intros)
    fix i1 i2 l
    assume *:"i1<x" and ***:"i2<x"
      and **:"accessStore (hash l1 (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) m1 = Some (MPointer l)"
    then have "MCon (MTArray x1 t) m1 l" using MTArray
      by (meson CompTypeRemainsMCon CompMemType.simps(2))
    moreover have "\<exists>l'. accessStore (hash l2 (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) m2 = Some (MPointer l')" using MTArray *** ** "*" MConArrayPointers gr_zeroI less_nat_zero_code by metis
    ultimately show "\<exists>l'. accessStore (hash l2 (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) m2 = Some (MPointer l') \<and> MCon (MTArray x1 t) m1 l \<and> MCon (MTArray x1 t) m2 l'"
      using MTArray.IH ** ***
      by (meson "*" CompTypeRemainsMCon MTArray.prems(2) CompMemType.simps(2))

  next
    fix i1 i2 val
    assume *:"i1<x" and ***:"i2<x"
      and **:" accessStore (hash l1 (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) m1 = Some (MValue val)"
    show "\<exists>val'. accessStore (hash l2 (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) m2 = Some (MValue val') \<and> MCon (MTArray x1 t) m1
        (hash l1 (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) \<and> MCon (MTArray x1 t) m2 (hash l2 (ShowL\<^sub>n\<^sub>a\<^sub>t i2))"
      using "*" "**" MTArray.prems(1) by fastforce
  qed
next
  case (MTValue x')
  show ?case
  proof(intros)
    fix i1 i2 l
    assume *:"i1<x" and ***:"i2<x"
      and **:"accessStore (hash l1 (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) m1 = Some (MPointer l)"
    show "\<exists>l'. accessStore (hash l2 (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) m2 = Some (MPointer l') \<and> MCon (MTValue x') m1 l \<and> MCon (MTValue x') m2 l'" using * ** MTValue by auto
  next
    fix i1 i2 val
    assume *:"i1<x" and ****:"i2<x"
      and **:"accessStore (hash l1 (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) m1 = Some (MValue val)"
    have ***:"(case accessStore (hash l2 (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) m2 of None \<Rightarrow> False
                 | Some (MValue val) \<Rightarrow> (case MTValue x' of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTValue x') m2 (hash l2 (ShowL\<^sub>n\<^sub>a\<^sub>t i2)))
                 | Some (MPointer loc2) \<Rightarrow> (case MTValue x' of MTArray len' arr' \<Rightarrow> MCon (MTValue x') m2 loc2 | MTValue Types \<Rightarrow> False))"
      using MTValue(2) MCon.simps(2)[of x "MTValue x'" m2 l2] * **** by simp
    then have "\<exists>l. accessStore (hash l2 (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) m2 = Some (MValue l)"
      by (auto split:option.splits mtypes.splits memoryvalue.splits)
    moreover have "MCon (MTValue x') m1 (hash l1 (ShowL\<^sub>n\<^sub>a\<^sub>t i1))" using * ** MTValue by auto
    ultimately show "\<exists>val'. accessStore (hash l2 (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) m2 = Some (MValue val') \<and> MCon (MTValue x') m1 (hash l1 (ShowL\<^sub>n\<^sub>a\<^sub>t i1))
                    \<and> MCon (MTValue x') m2 (hash l2 (ShowL\<^sub>n\<^sub>a\<^sub>t i2))" using *** by auto
  qed
qed


lemma SubPtrs_top:
  assumes "LSubPrefL2 stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem))"
    and "\<forall>l l'. LSubPrefL2 l (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem)) \<and> accessStore l mem' = Some (MPointer l') \<longrightarrow> l' = l"
    and "TypedMemSubPrefPtrs mem' x11 x12 stl2 dloc1"
  shows "LSubPrefL2 dloc1 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem))"
proof(cases x12)
  case (MTArray x11' x12')

  then obtain i l where idef:"i<x11 \<and> accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem' = Some (MPointer l) \<and> (l = dloc1 \<or> TypedMemSubPrefPtrs mem' x11' x12' l dloc1)"
    using assms by auto
  then have lsubloc:"LSubPrefL2 (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem))" using LSubPrefL2_def
    using assms(1) hash_suffixes_associative by auto
  then have lSelfPoint:"l = (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using assms idef by simp

  have lsubloc:"LSubPrefL2 l (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem))" using lsubloc lSelfPoint by simp

  then show ?thesis
  proof(cases "l = dloc1")
    case True
    then show ?thesis
      using lsubloc lSelfPoint by auto
  next
    case False
    then have lneq2:"\<forall>i<x11'. LSubPrefL2 (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem))" using lSelfPoint idef lsubloc
      by (metis LSubPrefL2_def Not_Sub_More_Specific)
    have "TypedMemSubPrefPtrs mem' x11' x12' l dloc1" using idef False by simp
    then show ?thesis using lneq2 lsubloc
    proof(induction x12' arbitrary:x11' l)
      case (MTArray x1 x12')
      have "\<exists>i'<x11'. \<exists>l'. accessStore (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i')) mem' = Some (MPointer l') \<and> (l' = dloc1 \<or> TypedMemSubPrefPtrs mem' x1 x12' l' dloc1)"
        using MTArray(2) unfolding TypedMemSubPrefPtrs.simps by simp
      then obtain i' l' where i'def:"i'<x11' \<and> accessStore (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i')) mem' = Some (MPointer l') \<and>
          (l' = dloc1 \<or> TypedMemSubPrefPtrs mem' x1 x12' l' dloc1)" by blast

      have l'subloc:"LSubPrefL2 (hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i')) (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mem))" using i'def LSubPrefL2_def
        using MTArray.prems(2) by auto
      then have l'SP:"(hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i')) = l'" using i'def assms by auto
      show ?case
      proof(cases "l' = dloc1")
        case True
        then show ?thesis using l'SP l'subloc by simp
      next
        case False
        then have "TypedMemSubPrefPtrs mem' x1 x12' l' dloc1" using i'def by simp
        moreover have "\<forall>i<x1. LSubPrefL2 (hash l' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (ShowL\<^sub>n\<^sub>a\<^sub>t(Toploc mem))"
          using l'subloc MemLSubPrefL2_specific_imps_general l'SP l'subloc
          by (metis LSubPrefL2_def Not_Sub_More_Specific)
        ultimately show ?thesis using MTArray.IH[of x1 l'] l'subloc l'SP by blast
      qed
    next
      case (MTValue x)


      then show ?case by auto
    qed
  qed
next
  case (MTValue x2)
  then show ?thesis
    using LSubPrefL2_def hash_suffixes_associative
    using assms(1,3) by auto
qed


lemma TypedMemSubPrefPtrs_trns:
  assumes "TypedMemSubPrefPtrs mem x2 t2 l2 l3"
    and "MCon (MTArray x1 t1) mem l1"
    and "CompMemType mem x1 t1 (MTArray x2 t2) l1 l2"
  shows "TypedMemSubPrefPtrs mem x1 t1 l1 l3" using assms
proof(induction t1 arbitrary:x1 l1)
  case (MTArray x1' t1')
  then have "(\<exists>i<x1. \<exists>l. accessStore (hash l1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l) \<and> (l = l2
      \<and> MTArray x1' t1' = MTArray x2 t2 \<or> CompMemType mem x1' t1' (MTArray x2 t2) l l2))"
    using CompMemType.simps(2)[of mem x1 x1' t1' "MTArray x2 t2" l1 l2] by auto
  then obtain i l where idef:"i<x1 \<and> accessStore (hash l1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l) \<and> (l = l2
      \<and> MTArray x1' t1' = MTArray x2 t2 \<or> CompMemType mem x1' t1' (MTArray x2 t2) l l2)"
    by blast
  then have mcond:"MCon (MTArray x1' t1') mem l" using MTArray(3)
    using CompTypeRemainsMCon CompMemType.simps(2) by blast

  then show ?case using TypedMemSubPrefPtrs.simps(2)[of mem x1 x1' t1' l1 l3] idef
    using MTArray.IH assms(1) assms(2) by blast
next
  case (MTValue x)
  then show ?case by simp
qed

lemma allocateMCon:
  assumes "MCon t mm loc"
    and "snd (allocate mm) = m'"
  shows "MCon t m' loc"
proof -
  have "\<forall>locs. accessStore locs mm = accessStore locs m'"
    using assms(2) unfolding allocate_def accessStore_def by auto
  then show ?thesis using assms(1)
  proof(induction t arbitrary:loc)
    case (MTArray x1 t)

    have "\<forall>i<x1.
            (case accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' of None \<Rightarrow> False
             | Some (MValue val) \<Rightarrow> (case t of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon t m' (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
             | Some (MPointer loc2) \<Rightarrow> (case t of MTArray len' arr' \<Rightarrow> MCon t m' loc2 | MTValue val \<Rightarrow> False))"
    proof intros
      fix i
      assume *:"i<x1"
      then show "(case accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' of None \<Rightarrow> False
             | Some (MValue val) \<Rightarrow> (case t of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon t m' (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
             | Some (MPointer loc2) \<Rightarrow> (case t of MTArray len' arr' \<Rightarrow> MCon t m' loc2 | MTValue val \<Rightarrow> False))"
      proof(cases t)
        case mta:(MTArray x11 x12)
        then obtain v where vDef:"accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mm = Some (MPointer v)
                                  \<and> MCon t mm v" using *
          by (metis MConArrayPointers MCon_imps_sub_Mcon MTArray.prems(2) MCon.simps(2))
        then show ?thesis using * MTArray mta by fastforce
      next
        case (MTValue x2)
        then obtain v where vDef:"accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mm = Some (MValue v)
                                  \<and> MCon t mm (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using *
          using MCon_imps_sub_Mcon MCon_sub_MTVal_imps_val MTArray.prems(2) by presburger
        then show ?thesis using MTArray.prems(1) MTValue by auto
      qed
    qed
    then show ?case unfolding MCon.simps using MTArray.prems
      by (metis MCon.simps(2))
  next
    case (MTValue x)
    then show ?case by simp
  qed
qed


lemma compMemTypes_trns:
  assumes "CompMemType mem len' arr' tp2 p' stl1"
    and "CompMemType mem len arr (MTArray len' arr') p'' p'"
  shows "CompMemType mem len arr tp2 p'' stl1" using assms
proof(induction arr arbitrary:p'' len)
  case (MTArray x1 arr)
  then show ?case by fastforce
next
  case (MTValue x)
  then show ?case by auto
qed

lemma Not_Sub_More_Specific_more_speific:
  assumes "\<not> TypedMemSubPref destl' destl (MTArray l t)"
  shows "\<not> (x<l \<and> TypedMemSubPref destl' (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t)" using assms by auto


lemma limitedMemoryChange:
  assumes "\<not>TypedMemSubPrefPtrs mem x t p'' prnt"
    and "p'' \<noteq> prnt"
    and "\<forall>locs. locs \<noteq> (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i)) \<longrightarrow> accessStore locs mem = accessStore locs mem'"
    and "\<exists>p. accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem' = Some (MPointer p)"
    and "MCon (MTArray x t) mem p''"
  shows "MCon (MTArray x t) mem' p''" using assms
proof (induction t arbitrary: x p'')
  case (MTArray x1 t)
  then have "x \<noteq> 0" using MCon.simps by blast
  moreover have "(\<exists>p. accessStore p'' mem' = Some (MPointer p)) \<or> accessStore p'' mem' = None"
  proof(cases "p'' = (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i))")
    case True
    then show ?thesis using MTArray by blast
  next
    case False
    then have "accessStore p'' mem = accessStore p'' mem'" using MTArray by simp
    then show ?thesis using MTArray MCon.simps \<open>x\<noteq>0\<close> by simp
  qed
  moreover have "\<forall>i<x. (case accessStore (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem' of None \<Rightarrow> False
                 | Some (MValue val) \<Rightarrow> (case (MTArray x1 t) of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon
                     (MTArray x1 t) mem' (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
                 | Some (MPointer loc2) \<Rightarrow> (case (MTArray x1 t) of MTArray len' arr' \<Rightarrow> MCon (MTArray x1 t) mem' loc2 | MTValue Types \<Rightarrow> False))"
  proof intros
    fix ii assume iiDef:"ii<x"
    show " case accessStore (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) mem' of None \<Rightarrow> False
         | Some (MValue val) \<Rightarrow> (case (MTArray x1 t) of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTArray x1 t) mem' (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t ii)))
         | Some (MPointer loc2) \<Rightarrow> (case (MTArray x1 t) of MTArray len' arr' \<Rightarrow> MCon (MTArray x1 t) mem' loc2 | MTValue Types \<Rightarrow> False)"
    proof(cases " (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) = (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i))")
      case True
      then have "p'' = prnt" using ShowLNatDot
        using hash_injective by blast
      then show ?thesis using MTArray by simp
    next
      case False
      then have same:"accessStore (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) mem = accessStore (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) mem'" using MTArray by simp
      then obtain v where "accessStore (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) mem' = Some (MPointer v) \<and> MCon (MTArray x1 t) mem v"
        using MTArray iiDef MCon_imps_sub_Mcon
        by (metis MConArrayPointers bot_nat_0.not_eq_extremum calculation(1))
      then show ?thesis using MTArray.IH[of x1 v ] MTArray.prems iiDef same by fastforce
    qed
  qed
  ultimately show ?case by simp
next
  case (MTValue x')
  then have "x \<noteq> 0" using MCon.simps by auto
  moreover have "(\<exists>p. accessStore p'' mem' = Some (MPointer p)) \<or> accessStore p'' mem' = None"
  proof(cases "p'' = (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i))")
    case True
    then show ?thesis using MTValue by blast
  next
    case False
    then have "accessStore p'' mem = accessStore p'' mem'" using MTValue by simp
    then show ?thesis using MTValue MCon.simps \<open>x\<noteq>0\<close> by simp
  qed
  moreover have "\<forall>i<x. (case accessStore (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem' of None \<Rightarrow> False
                 | Some (MValue val) \<Rightarrow> (case MTValue x' of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTValue x') mem' (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
                 | Some (MPointer loc2) \<Rightarrow> (case MTValue x' of MTArray len' arr' \<Rightarrow> MCon (MTValue x') mem' loc2 | MTValue Types \<Rightarrow> False))"
  proof intros
    fix ii assume iiDef:"ii<x"
    show " case accessStore (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) mem' of None \<Rightarrow> False
         | Some (MValue val) \<Rightarrow> (case MTValue x' of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon (MTValue x') mem' (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t ii)))
         | Some (MPointer loc2) \<Rightarrow> (case MTValue x' of MTArray len' arr' \<Rightarrow> MCon (MTValue x') mem' loc2 | MTValue Types \<Rightarrow> False)"
    proof(cases " (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) = (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i))")
      case True
      then have "p'' = prnt" using ShowLNatDot
        using hash_injective by blast
      then show ?thesis using MTValue by simp
    next
      case False
      then have same:"accessStore (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) mem = accessStore (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) mem'" using MTValue by simp
      then obtain v where "accessStore (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) mem' = Some (MValue v) \<and> MCon (MTValue x') mem (hash p'' (ShowL\<^sub>n\<^sub>a\<^sub>t ii))" using MTValue
          MCon_sub_MTVal_imps_val iiDef by (metis MCon_imps_sub_Mcon)
      then show ?thesis using same by auto
    qed
  qed
  ultimately show ?case using MCon.simps(2)[of x "MTValue x'" mem p''] by simp
qed

lemma mconCopySingle:
  assumes "\<forall>locs. \<not> LSubPrefL2 locs l \<longrightarrow> accessStore locs cd' = accessStore locs c''"
    and"\<forall>loc. LSubPrefL2 loc l \<longrightarrow> accessStore loc cd' = None"
    and "MCon struct cd' x2"
  shows "MCon struct c'' x2" using assms(3)
proof(induction struct arbitrary:x2)
  case (MTArray x1 struct')
  then show ?case
  proof(cases "x1 = 0")
    case True
    then show ?thesis using MTArray by simp
  next
    case False
    then have a10:"\<forall>(i::nat)<x1.
             case accessStore (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) cd' of None \<Rightarrow> False
             | Some (MValue val) \<Rightarrow> (case struct' of MTValue typ \<Rightarrow> MCon struct' cd' (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) | _ \<Rightarrow> False)
             | Some (MPointer loc2) \<Rightarrow> (case struct' of MTArray len' arr' \<Rightarrow> MCon struct' cd' loc2 | MTValue Types \<Rightarrow> False)"
      using MCon.simps(2)[of x1 struct' cd' x2] MTArray by simp
    have "\<forall>i<x1.
             case accessStore (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) c'' of None \<Rightarrow> False
             | Some (MValue val) \<Rightarrow> (case struct' of MTValue typ \<Rightarrow> MCon struct' c'' (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) | _ \<Rightarrow> False)
             | Some (MPointer loc2) \<Rightarrow> (case struct' of MTArray len' arr' \<Rightarrow> MCon struct' c'' loc2 | MTValue Types \<Rightarrow> False)"
    proof intros
      fix i assume a20:"i<x1"
      then obtain x where xdef:"accessStore (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) cd' = Some x" using a10 by fastforce
      then have "\<not> LSubPrefL2 (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) l" using assms by auto
      then have same:"accessStore (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) c'' = Some x" using assms(1) xdef by simp
      then show " case accessStore (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) c'' of None \<Rightarrow> False
             | Some (MValue val) \<Rightarrow> (case struct' of MTValue typ \<Rightarrow> MCon struct' c'' (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) | _ \<Rightarrow> False)
             | Some (MPointer loc2) \<Rightarrow> (case struct' of MTArray len' arr' \<Rightarrow> MCon struct' c'' loc2 | MTValue Types \<Rightarrow> False)"
      proof(cases "x")
        case (MValue x1')
        then show ?thesis
        proof(cases struct')
          case (MTArray x11 x12)
          then show ?thesis using a10 a20 xdef MValue by auto
        next
          case (MTValue x2')
          then have "MCon struct' cd' (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using a10 a20 xdef MValue by auto
          then show ?thesis using same MValue MTValue MTArray(1) by force
        qed
      next
        case (MPointer x2)
        then show ?thesis
        proof(cases struct')
          case mtr:(MTArray x11 x12)
          then have "MCon struct' cd' x2" using a10 a20 xdef MPointer
            by fastforce
          then show ?thesis using same MPointer MTArray(1) mtr
            by fastforce
        next
          case (MTValue x2')
          then show ?thesis using a10 a20 xdef MPointer by auto
        qed
      qed

    qed
    moreover have "(\<exists>p. accessStore x2 c'' = Some (MPointer p)) \<or> accessStore x2 c'' = None"
      by (metis (no_types, lifting) MTArray.prems LSubPrefL2_def assms(1) assms(2) hash_suffixes_associative option.case_eq_if MCon.simps(2))
    ultimately show ?thesis using MCon.simps(2)[of x1 struct' c'' x2]
      using False by auto
  qed
next
  case (MTValue x)
  then have "(case accessStore x2 cd' of None \<Rightarrow> False
            | Some (MValue t) \<Rightarrow> typeCon x t
            | Some (MPointer t) \<Rightarrow> False)"
    using MCon.simps(1)[of x cd' x2] by simp
  then obtain t where "accessStore x2 cd' = Some (MValue t)"
    by (simp split:option.splits memoryvalue.splits)
  then have "\<not>LSubPrefL2 x2 l" using assms(2) by auto
  then show ?case using MTValue assms by simp
qed


lemma mcon_accessStore:
  assumes "MCon (MTArray len arr) cd loc"
    and "len > 0"
    and "i<len"
  obtains (1) loc2 len' arr'
  where "accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) cd = Some (MPointer loc2)"
    and "arr = MTArray len' arr'"
  | (2) val tp
  where "accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) cd = Some (MValue val)"
    and "arr = MTValue tp"
proof(cases "accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) cd")
  case None
  then show ?thesis using assms MCon.simps by auto
next
  case (Some a)
  then show ?thesis
  proof(cases a)
    case (MValue x1)
    then show ?thesis
    proof(cases arr)
      case (MTArray x11 x12)
      then show ?thesis using Some MValue MCon.simps assms by auto
    next
      case (MTValue x2)
      then show ?thesis using Some MValue MCon.simps assms by (simp add: "2")
    qed
  next
    case (MPointer x2)
    then show ?thesis
    proof(cases arr)
      case (MTArray x11 x12)
      then show ?thesis using Some MPointer MCon.simps assms by (simp add: "1")
    next
      case (MTValue x2)
      then show ?thesis using Some MPointer MCon.simps assms by auto
    qed
  qed
qed

lemma SameMCon_imps_MConAccessSame:
  assumes "MCon t m1 l1"
    and "MCon t m2 l2"
  shows "MConAccessSame l1 l2 t m1 m2" using assms
proof(induction t arbitrary: l1 l2)
  case (MTArray x1 t)
  show ?case unfolding MConAccessSame.simps
  proof(intros)
    fix i1 i2 l
    assume *:"i1 <x1" and **:"i2<x1" and ***:" accessStore (hash l1 (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) m1 = Some (MPointer l)"
    then have "\<exists>l'. accessStore (hash l2 (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) m2 = Some (MPointer l')" using MTArray.prems(2)
      by (metis MTArray.prems(1) mtypes.distinct(1) memoryvalue.distinct(1) gr_zeroI less_nat_zero_code mcon_accessStore option.inject)
    then obtain l' where l'def:"accessStore (hash l2 (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) m2 = Some (MPointer l')" by blast
    moreover have "MCon t m1 l" using MTArray.prems(1) * ***
      using MCon_imps_sub_Mcon by blast
    moreover have "MCon t m2 l'" using ** l'def MTArray.prems(2)
      using MCon_imps_sub_Mcon by blast
    ultimately have "MConAccessSame l l' t m1 m2" using MTArray.IH[of l l'] using MTArray.prems *** * ** by simp
    then show "\<exists>l'. accessStore (hash l2 (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) m2 = Some (MPointer l') \<and> MConAccessSame l l' t m1 m2 " using l'def by simp
  qed
next
  case (MTValue x)
  then have mc1:" case accessStore l1 m1 of None \<Rightarrow> False | Some (MValue xb) \<Rightarrow> typeCon x xb | Some (MPointer t) \<Rightarrow> False"
    unfolding MCon.simps by simp
  have mc2:"case accessStore l2 m2 of None \<Rightarrow> False | Some (MValue xb) \<Rightarrow> typeCon x xb | Some (MPointer t) \<Rightarrow> False"
    using MTValue unfolding MCon.simps by simp
  have "\<exists>val. accessStore l1 m1 = Some (MValue val) \<and> (\<exists>val'. accessStore l2 m2 = Some (MValue val'))"
    using mc2 mc1 by (auto split:option.splits memoryvalue.splits)
  then show ?case unfolding MConAccessSame.simps by blast
qed

lemma MCon_imps_TypedMemSubPref_Some:
  assumes "TypedMemSubPref x' loc t"
    and "MCon t m loc"
    and "\<forall>l l'. TypedMemSubPref l loc t \<and> accessStore l m = Some (MPointer l') \<longrightarrow> l' = l"
  shows "\<exists>v. accessStore x' m = Some v"
  using assms
proof(induction t arbitrary:loc)
  case (MTArray x1 t)
  then have a1:"(\<exists>i<x1. TypedMemSubPref x' (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t \<or> x' = hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i))"
    using TypedMemSubPref.simps(2)[of x' loc x1 t] by simp
  then have "x1 > 0" using not_less_zero by auto
  then have mcon_array: "x1 > 0 \<and> (\<forall>j<x1. case accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t j)) m of
                                     None \<Rightarrow> False
                                   | Some (MValue val) \<Rightarrow> (case t of MTValue typ \<Rightarrow> MCon t m (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t j)) | _ \<Rightarrow> False)
                                   | Some (MPointer loc2) \<Rightarrow> (case t of MTArray len' arr' \<Rightarrow> MCon t m loc2 | MTValue typ \<Rightarrow> False))
                        \<and> (\<exists>p. accessStore loc m = Some (MPointer p) \<or> accessStore loc m = None)"
    using MTArray.prems(2) MCon.simps(2)[of x1 t m loc] by simp
  then have som:"\<forall>j<x1. \<exists>v. accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t j)) m = Some v"
    using mcon_accessStore
    by fastforce
  then show ?case
  proof(cases "\<exists>i<x1. x' = hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)")
    case True
    then show ?thesis using som by blast
  next
    case False
    then obtain i where iDef:"i<x1 \<and> TypedMemSubPref x' (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t" using a1 by blast
    then obtain v where vDef: "accessStore (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some v" using som by blast
    then show ?thesis
    proof(cases v)
      case (MValue x1)
      then show ?thesis using iDef MTArray.IH vDef mcon_array
        by (metis MTArray.prems(2) memoryvalue.simps(4) TypedMemSubPref.simps(1) mcon_accessStore option.inject)
    next
      case (MPointer x2)
      then have "x2 = (hash loc (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using iDef MTArray.prems(3)
        using TypedMemSubPref.simps(2) vDef by blast
      then show ?thesis using MTArray.IH iDef vDef mcon_array
        by (metis MCon_imps_sub_Mcon MPointer MTArray.prems(2,3) TypedMemSubPref.simps(2))
    qed
  qed
next
  case (MTValue x)
  then show ?case
    by (metis MConAccessSame.simps(1) SameMCon_imps_MConAccessSame TypedMemSubPref.simps(1))
qed

lemma mcon_typedptrs_imps_existence:
  assumes "MCon (MTArray x t) m1 l1"
  shows "\<forall>l1'. TypedMemSubPrefPtrs m1 x t l1 l1' \<longrightarrow> (\<exists>t. MCon t m1 l1')" using assms(1)
proof(induction t arbitrary:x l1)
  case (MTArray x1 t)
  then show ?case
    by (metis MCon_imps_sub_Mcon TypedMemSubPrefPtrs.simps(2))
next
  case (MTValue x)
  then show ?case
    using CompTypeRemainsMCon TypedMemSubPrefPtrs.simps(1) CompMemType.simps(1) by blast
qed

lemma memSet_selfPoint:
  assumes "MCon t' m tL"
    and "x'' \<in> GetAllMemoryLocations t' tL m"
    and "\<forall>l l'. TypedMemSubPref l tL t' \<and> accessStore l m = Some (MPointer l') \<longrightarrow> l' = l"
    and "accessStore x'' m = Some (MPointer locs')"
  shows "locs' = x''" using assms
proof(induction t' arbitrary:tL)
  case (MTArray x1 t')
  obtain i where idef: "i\<in>{0..<x1} \<and> x'' \<in> (case accessStore (hash tL (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m of None
      \<Rightarrow> {} | Some (MValue xa) \<Rightarrow> {hash tL (ShowL\<^sub>n\<^sub>a\<^sub>t i)} \<union> GetAllMemoryLocations t' (hash
      tL (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m
           | Some (MPointer ptr) \<Rightarrow> {hash tL (ShowL\<^sub>n\<^sub>a\<^sub>t i)} \<union> GetAllMemoryLocations t' ptr m)"
    using MTArray.prems unfolding GetAllMemoryLocations.simps by blast
  then consider (ptr) ptr where "i<x1 \<and> accessStore (hash tL (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some (MPointer ptr) \<and> x''
      \<in> {hash tL (ShowL\<^sub>n\<^sub>a\<^sub>t i)} \<union> GetAllMemoryLocations t' ptr m"
    | (val) val where "i<x1 \<and> accessStore (hash tL (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some (MValue val) \<and> x'' \<in> {hash tL
        (ShowL\<^sub>n\<^sub>a\<^sub>t i)} \<union> GetAllMemoryLocations t' (hash tL (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m"
    by (auto split:option.splits memoryvalue.splits)
  then show ?case
  proof(cases)
    case ptr
    then have subL:"TypedMemSubPref (hash tL (ShowL\<^sub>n\<^sub>a\<^sub>t i)) tL (MTArray x1 t')" by auto
    then have ptrSame:"ptr = (hash tL (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using MTArray.prems(3) ptr by blast

    then show ?thesis
    proof(cases "x'' = hash tL (ShowL\<^sub>n\<^sub>a\<^sub>t i)")
      case True
      then show ?thesis
        using MTArray.prems(3) assms(4) subL by blast
    next
      case False
      then have a0:"x'' \<in> GetAllMemoryLocations t' ptr m" using ptr by simp
      moreover have "MCon t' m ptr" using MTArray.prems(1) ptr
        using MCon_imps_sub_Mcon by blast
      moreover have "\<forall>l l'. TypedMemSubPref l ptr t' \<and> accessStore l m = Some (MPointer l') \<longrightarrow> l' = l"
        using MTArray.prems(3) Not_Sub_More_Specific_more_speific ptr ptrSame by blast
      ultimately have "locs' = x''" using MTArray.IH[OF _ a0] MTArray.prems(4) by blast
      then show ?thesis by blast
    qed
  next
    case val
    then have "\<exists>v'. t' = MTValue v'" using MTArray.prems(1)
      by (metis memoryvalue.distinct(1) mcon_accessStore neq0_conv option.inject order_less_trans)
    then have "x'' = hash tL (ShowL\<^sub>n\<^sub>a\<^sub>t i)" using val by auto
    then show ?thesis using MTArray val by auto
  qed
next
  case (MTValue x)
  then show ?case by auto
qed


lemma moreSpecificTypedSubPref:
  assumes "( \<forall>l l'. TypedMemSubPref l destl (MTArray x t) \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l)"
  shows "\<forall>i<x. ( \<forall>l l'. TypedMemSubPref l (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l)" using assms(1)
proof (induction t arbitrary:x)
  case (MTArray x1 t)
  show ?case
  proof intros
    fix i l l'
    assume *:"i<x"
      and **:"TypedMemSubPref l (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) (MTArray x1 t) \<and> accessStore l v' = Some (MPointer l')"
    then show "l' =l" using MTArray(1) * **
      by (meson MTArray.prems Not_Sub_More_Specific_more_speific)
  qed
next
  case (MTValue x)
  then show ?case by auto
qed

lemma MCon_mem_preserved_disjoint_update:
  assumes "(\<not>LSubPrefL2 destl' destl) \<and> \<not>LSubPrefL2 destl destl' "
  shows "(\<forall>l l'. TypedMemSubPref l destl' t' \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l)
          \<and> (\<forall>destl'. \<not> LSubPrefL2 destl' destl \<longrightarrow> accessStore destl' v' = accessStore destl' v'')
          \<and> MCon t' v' destl' \<longrightarrow> MCon t' v'' destl'" using assms
proof(induction t' arbitrary:destl' )
  case (MTArray x1 t)
  show ?case
  proof intros
    assume "(\<forall>l l'. TypedMemSubPref l destl' (MTArray x1 t) \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l)
              \<and> (\<forall>destl'. \<not> LSubPrefL2 destl' destl \<longrightarrow> accessStore destl' v' = accessStore destl' v'')
              \<and> MCon (MTArray x1 t) v' destl'
              "
    then have *:"(\<forall>l l'. TypedMemSubPref l destl' (MTArray x1 t) \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l)"
      and **: "MCon (MTArray x1 t) v' destl'"
      and ***:"(\<forall>destl'. \<not> LSubPrefL2 destl' destl \<longrightarrow> accessStore destl' v' = accessStore destl' v'')"
      by blast+


    then show "MCon (MTArray x1 t) v'' destl'"
    proof (cases "x1>0")
      case True
      have a10:"\<forall>i<x1.
             case accessStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' of None \<Rightarrow> False
              | Some (MValue val) \<Rightarrow> (case t of MTValue typ \<Rightarrow> MCon t v' (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) | _ \<Rightarrow> False)
             | Some (MPointer loc2) \<Rightarrow> (case t of MTArray len' arr' \<Rightarrow> MCon t v' loc2 | MTValue Types \<Rightarrow> False)"
        using ** by auto


      have "\<forall>i<x1.
             case accessStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' of None \<Rightarrow> False
              | Some (MValue val) \<Rightarrow> (case t of MTValue typ \<Rightarrow> MCon t v'' (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) | _ \<Rightarrow> False)
             | Some (MPointer loc2) \<Rightarrow> (case t of MTArray len' arr' \<Rightarrow> MCon t v'' loc2 | MTValue Types \<Rightarrow> False)"
      proof intros
        fix i
        assume iLess: "i<x1"
        show "case accessStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' of None \<Rightarrow> False
                  | Some (MValue val) \<Rightarrow> (case t of MTValue typ \<Rightarrow> MCon t v'' (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) | _\<Rightarrow> False)
                  | Some (MPointer loc2) \<Rightarrow> (case t of MTArray len' arr' \<Rightarrow> MCon t v'' loc2 | MTValue Types \<Rightarrow> False)"
        proof(cases t)
          case mtr:(MTArray x11 x12)
          have b100:"\<not> LSubPrefL2 (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) destl" using Mutual_NonSub_SpecificNonSub MTArray by auto
          then have "\<not> LSubPrefL2 destl (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using Not_Sub_More_Specific MTArray by auto
          then have a50:"(\<forall>l l'. TypedMemSubPref l (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l)
                          \<and> (\<forall>destl'. \<not> LSubPrefL2 destl' destl \<longrightarrow> accessStore destl' v' = accessStore destl' v'')
                          \<and> MCon t v' (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) \<longrightarrow>
                          MCon t v'' (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i))
            " using MTArray(1)[of "(hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i))"] b100 hash_suffixes_associative by blast
          have a55:"\<forall>l l'. TypedMemSubPref l (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t \<and> accessStore l v' = Some
              (MPointer l') \<longrightarrow> l' = l" using * moreSpecificTypedSubPref[of destl' x1 t v'] iLess by blast
          then have a60:"accessStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = accessStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v''" using b100 *** by blast
          then show ?thesis
          proof(cases "accessStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'")
            case None
            then show ?thesis using a10 iLess by auto
          next
            case (Some a)
            then show ?thesis
            proof(cases a)
              case (MValue x1)
              then show ?thesis using a10 iLess mtr Some by auto
            next
              case (MPointer x2')
              then have x2'def:"x2' = (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using a55 Some *
                using iLess TypedMemSubPref.simps(2) by blast
              then have "MCon t v' (x2')" using a10 iLess Some mtr MPointer
                by fastforce
              then have "MCon t v'' x2'" using a50 b100 a55 *** x2'def by auto
              then show ?thesis using Some MPointer mtr a60 by auto
            qed
          qed
        next
          case (MTValue x2)
          have b100:"\<not> LSubPrefL2 (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) destl" using Mutual_NonSub_SpecificNonSub MTArray by auto
          then have "\<not> LSubPrefL2 destl (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using Not_Sub_More_Specific MTArray by auto
          then have a50:"(\<forall>destl'. \<not> LSubPrefL2 destl' destl \<longrightarrow> accessStore destl' v' = accessStore destl' v'') \<and>
                           MCon t v' (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) \<longrightarrow>
                          MCon t v'' (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i))
            " using MTArray(1)[of "(hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i))"] b100 using MTValue by force
          then have a60:"accessStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = accessStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v''" using b100 *** by simp
          then show ?thesis
          proof(cases "accessStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'")
            case None
            then show ?thesis using a10 iLess by auto
          next
            case (Some a)
            then show ?thesis
            proof(cases a)
              case (MValue x1)
              then have "MCon t v' (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using a10 iLess Some MTValue by auto
              then have "MCon t v'' (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using a50 b100 a60 *** Some MValue by auto
              then show ?thesis using Some MValue MTValue a60 by auto
            next
              case (MPointer x2')
              then show ?thesis using a10 iLess MTValue Some by auto
            qed

          qed

        qed

      qed

      moreover have "(\<exists>p. accessStore destl' v'' = Some (MPointer p)) \<or> accessStore destl' v'' = None" using ** MCon.simps(2)
        using MTArray.prems True \<open>(\<forall>l l'. TypedMemSubPref l destl' (MTArray x1 t) \<and> accessStore l v' = Some (MPointer l')
            \<longrightarrow> l' = l) \<and> (\<forall>destl'. \<not> LSubPrefL2 destl' destl \<longrightarrow> accessStore destl' v' =
            accessStore destl' v'') \<and> MCon (MTArray x1 t) v' destl'\<close> by auto
      ultimately show ?thesis using MCon.simps(2)[of x1 t v'' destl']
        by (simp add: True)
    next
      case False
      then show ?thesis using ** by simp
    qed

  qed
next
  case (MTValue x)
  show ?case
  proof intros
    assume "(\<forall>l l'. TypedMemSubPref l destl' (MTValue x) \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l) \<and>
    (\<forall>destl'. \<not> LSubPrefL2 destl' destl \<longrightarrow> accessStore destl' v' = accessStore destl' v'') \<and>
MCon (MTValue x) v' destl' "
    then have *:"(\<forall>destl'. \<not> LSubPrefL2 destl' destl \<longrightarrow> accessStore destl' v' = accessStore destl' v'')"
      and **:"MCon (MTValue x) v' destl'"
      and ***:"(\<forall>l len tp.
        MTValue x = MTArray len tp \<and> MCon (MTValue x) v' destl' \<longrightarrow>
        (\<forall>i<len. accessStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = Some (MPointer l) \<and> l = hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)))"
      by auto+
    then have "accessStore destl' v' = accessStore destl' v''" using MTValue by simp
    then show "MCon (MTValue x) v'' destl'" using ** by simp
  qed
qed


subsection \<open>Typed sub-prefixes\<close>

lemma mtype_size_strict_decrease_array: "mtype_size arr < mtype_size (MTArray len arr)"
  by (simp)

lemma neg_MemLSubPrefL2_imps_TypedMemSubPref:
  assumes "\<not>LSubPrefL2 l1 l2"
  shows "\<not>TypedMemSubPref l1 l2 t" using assms
proof(induction t arbitrary:l2)
  case (MTArray x1 t)
  then show ?case
    by (simp add: LSubPrefL2_def hash_suffixes_associative)
next
  case (MTValue x)
  then show ?case
    by (simp add: LSubPrefL2_def)
qed

abbreviation mymemory::memoryT
  where "mymemory \<equiv>
    \<lparr>Mapping = fmap_of_list
      [(STR ''1.1.0'', MValue STR ''False''),
       (STR ''0.1.0'', MValue STR ''True''),
       (STR ''1.0'', MPointer STR ''1.0''),
       (STR ''1.0.0'', MValue STR ''False''),
       (STR ''0.0.0'', MValue STR ''True''),
       (STR ''0.0'', MPointer STR ''0.0'')],
     Toploc = 1,
     Typed_Mapping = fmap_of_list
      [(STR ''1.1.0'', MTValue TBool),
       (STR ''0.1.0'', MTValue TBool),
       (STR ''1.0'', MTArray 2 (MTValue TBool)),
       (STR ''1.0.0'', MTValue TBool),
       (STR ''0.0.0'', MTValue TBool),
       (STR ''0.0'', MTArray 2 (MTValue TBool))]\<rparr>"


lemma reversible_CompMemJustType_imps_same:
  assumes "CompMemJustType t1 t2"
    and "CompMemJustType t2 t1"
  shows "t1 = t2"
  using assms
proof (induction t1 arbitrary: t2)
  case (MTValue tp)
  then show ?case by simp
next
  case (MTArray len arr)
  then obtain len2 arr2 where a10:"t2 = MTArray len2 arr2"
    using CompMemJustType.simps
    by (metis mtypes.exhaust)

  then show ?case
  proof(cases "len2 = len \<and> arr2 = arr")
    case True
    then show ?thesis using a10 by auto
  next
    case False
    then have "CompMemJustType arr arr2"
      using MTArray.prems(1) a10
      by (metis CompMemTypes_asc mtypes.exhaust mtypes.inject(1) CompMemJustType.simps(1) CompMemJustType.simps(2))
    moreover have "CompMemJustType arr2 arr" using a10 MTArray.prems False
      by (metis CompMemJustType.simps(1,2) CompMemTypes_asc less_not_refl mtype_size.cases mtype_size_strict_decrease_array)
    ultimately have "arr = arr2"
      using MTArray.IH by auto
    then show ?thesis using MTArray \<open>CompMemJustType arr2 arr\<close> \<open>t2 = MTArray len2 arr2\<close> by force
  qed
qed


lemma CompMemTypeSameLocsSameType:
  assumes "MCon (MTArray len arr) mem p'"
    and "CompMemType mem len arr tp1 p' stl1"
    and "CompMemType mem len arr tp2 p' stl1"
  shows "tp2 = tp1"
  using MCon_CompMemJustType_unique[OF CompMemType_imps_CompMemJustType[OF assms(3)]
      CompMemType_imps_CompMemJustType[OF assms(2)]
      CompTypeRemainsMCon[OF assms(3,1)] CompTypeRemainsMCon[OF assms(2,1)]] .

lemma CompMemType_asc_withSharedTarget:
  assumes "CompMemType mem len x (MTArray x' t') p' stl2"
    and "CompMemType mem len x tp1 p' stl1"
    and "MCon (MTArray len x) mem p'"
    and "TypedMemSubPrefPtrs mem x' t' stl2 stl1"
  shows "CompMemType mem x' t' tp1 stl2 stl1" using assms(1,3,4)
proof(induction t' arbitrary:stl2 x')
  case (MTArray x1 t')
  have mc2:"MCon (MTArray x' (MTArray x1 t')) mem stl2" using CompTypeRemainsMCon[OF MTArray.prems(1,2)] by simp
  have "(\<exists>i<x'. \<exists>l. accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l)
        \<and> (l = stl1 \<or> TypedMemSubPrefPtrs mem x1 t' l stl1))"
    using MTArray TypedMemSubPrefPtrs.simps(2)[of mem x' x1 t' stl2 stl1] by simp
  then obtain i l where idef:"i<x'" and ldef:"accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l) \<and> (l = stl1 \<or> TypedMemSubPrefPtrs mem x1 t' l stl1)" by blast
  have MConexpand:" \<forall>i<x'.
             (case accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem of None \<Rightarrow> False
              | Some (MValue val) \<Rightarrow> (case MTArray x1 t' of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon
                  (MTArray x1 t') mem (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
              | Some (MPointer loc2) \<Rightarrow> (case MTArray x1 t' of MTArray len' arr' \<Rightarrow> MCon (MTArray x1 t') mem loc2 | MTValue Types \<Rightarrow> False)) \<and>
             ((\<exists>p. accessStore stl2 mem = Some (MPointer p)) \<or> accessStore stl2 mem = None)"
    using mc2 MTArray.prems MCon.simps(2)[of x' "(MTArray x1 t')" mem stl2] by simp
  have " (accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l) \<and> (l = stl1 \<and> MTArray x1 t' = tp1 \<or> CompMemType mem x1 t' tp1 l stl1))"
  proof(cases "l = stl1")
    case True
    then show ?thesis
      by (metis CompMemTypeSameLocsSameType MTArray.prems(1) assms(2) assms(3) compMemTypes_trns idef ldef CompMemType.simps(2))
  next
    case False
    then have "TypedMemSubPrefPtrs mem x1 t' l stl1" using ldef by simp
    then show ?thesis
      by (meson CompTypeRemainsMCon MTArray.IH MTArray.prems(1) assms(2) assms(3) compMemTypes_trns idef ldef CompMemType.simps(2))
  qed
  then show ?case using CompMemType.simps(2)[of mem x' x1 t' tp1 stl2 stl1] idef ldef by blast
next
  case (MTValue x)
  then show ?case
    by (metis CompMemTypeSameLocsSameType TypedMemSubPrefPtrs.simps(1) assms(2) compMemTypes_trns CompMemType.simps(1))
qed

lemma TypedMemSubPrefOneWay:
  assumes "TypedMemSubPrefPtrs mem x1 t1 stl1 stl2"
    and "CompMemJustType (MTArray x1 t1) (MTArray x2 t2)"
    and "MCon (MTArray x1 t1) mem stl1"
    and "MCon (MTArray x2 t2) mem stl2"
    and "CompMemType mem x1 t1 (MTArray x2 t2) stl1 stl2"
  shows "\<not>TypedMemSubPrefPtrs mem x2 t2 stl2 stl1"
  using assms
proof(induction t2 arbitrary:x2 stl2)
  case (MTArray x2' t2')
  then show ?case
  proof(induction t1 arbitrary: x1 stl1)
    case (MTArray x1' t1')
    show ?case
    proof
      assume *:"TypedMemSubPrefPtrs mem x2 (MTArray x2' t2') stl2 stl1"
      then have a10:"(\<exists>i<x2. \<exists>l. accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l) \<and> (l = stl1 \<or> TypedMemSubPrefPtrs mem x2' t2' l stl1))"
        using TypedMemSubPrefPtrs.simps(2)[of mem x2 x2' t2' stl2 stl1] by simp
      have a20:"(\<exists>i<x1. \<exists>l. accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l) \<and> (l = stl2 \<or> TypedMemSubPrefPtrs mem x1' t1' l stl2))"
        using MTArray(3) TypedMemSubPrefPtrs.simps(2)[of mem x1 x1' t1' stl1 stl2] by simp
      have a30:"\<forall>i<x1.
             (case accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem of None \<Rightarrow> False
              | Some (MValue val) \<Rightarrow> (case MTArray x1' t1' of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon
                  (MTArray x1' t1') mem (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
              | Some (MPointer loc2) \<Rightarrow> (case MTArray x1' t1' of MTArray len' arr' \<Rightarrow> MCon (MTArray x1' t1') mem loc2 | MTValue Types \<Rightarrow> False))
            \<and> ((\<exists>p. accessStore stl1 mem = Some (MPointer p)) \<or> accessStore stl1 mem = None)"
        using MTArray MCon.simps(2)[of x1 "MTArray x1' t1'" mem stl1] by simp
      have a40:"\<forall>i<x2.
             (case accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem of None \<Rightarrow> False
              | Some (MValue val) \<Rightarrow> (case MTArray x2' t2' of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon
                  (MTArray x2' t2') mem (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
              | Some (MPointer loc2) \<Rightarrow> (case MTArray x2' t2' of MTArray len' arr' \<Rightarrow> MCon (MTArray x2' t2') mem loc2 | MTValue Types \<Rightarrow> False)) \<and>
             ((\<exists>p. accessStore stl2 mem = Some (MPointer p)) \<or> accessStore stl2 mem = None)"
        using MTArray MCon.simps(2)[of x2 "MTArray x2' t2'" mem stl2] by simp
      obtain i1 l1 where i1def:"i1<x1 \<and> accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i1)) mem = Some (MPointer l1) \<and> (l1 = stl2 \<or> TypedMemSubPrefPtrs mem x1' t1' l1 stl2)"
        using a20 by blast
      obtain i2 l2 where i2def:"i2<x2 \<and> accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i2)) mem = Some (MPointer l2) \<and> (l2 = stl1 \<or> TypedMemSubPrefPtrs mem x2' t2' l2 stl1)"
        using a10 by blast
      show False
      proof(cases "l1 = stl2")
        case t1:True
        then show ?thesis
        proof(cases "l2 = stl1")
          case t2:True
          then have "MCon (MTArray x1' t1') mem stl2" using t1 i2def i1def a30 by fastforce
          have b1:"MCon (MTArray x2' t2') mem stl1" using t1 t2 i2def i1def a40 by fastforce
          have b2:"MCon (MTArray x1 (MTArray x1' t1')) mem stl1" using MTArray by simp


          show ?thesis using b1 MTArray.prems(3,4,5)
            by (metis MConSubTypes \<open>MCon (MTArray x1' t1') mem stl2\<close> CompMemJustType.simps(2))
        next
          case False
          then have "TypedMemSubPrefPtrs mem x2' t2' l2 stl1" using i2def by simp
          moreover have "TypedMemSubPrefPtrs mem x1 (MTArray x1' t1') stl1 l2" using MTArray.prems(2) i2def
            using MTArray.prems(4,5,6) TypedMemSubPrefPtrs.simps(2) TypedMemSubPrefPtrs_trns by blast
          moreover have "CompMemJustType (MTArray x1 (MTArray x1' t1')) (MTArray x2' t2')" using MTArray
            by (metis CompMemTypes_asc CompMemJustType.simps(2))
          moreover have "MCon (MTArray x1 (MTArray x1' t1')) mem stl1" using MTArray.prems by auto
          moreover have "MCon (MTArray x2' t2') mem l2" using i2def a40 by fastforce
          moreover have "CompMemType mem x1 (MTArray x1' t1') (MTArray x2' t2') stl1 l2"
            by (meson MTArray.prems(6) compMemTypes_trns i2def CompMemType.simps(2))
          ultimately show ?thesis using MTArray(2)[of l2 x2'] by blast
        qed
      next
        case False
        then show ?thesis
        proof(cases "l2 = stl1")
          case t2:True
          have "TypedMemSubPrefPtrs mem x1' t1' l1 stl2" using False
            using i1def by auto
          then show ?thesis using t2
            by (metis CompMemType.simps(2) MConPtrsMustBeSubLocs_CompMemType MCon_imps_sub_Mcon MTArray.prems(4,5,6) compMemTypes_trns i2def)
        next
          case f2:False
          then have "TypedMemSubPrefPtrs mem x1' t1' l1 stl2" using i1def False by simp
          moreover have "TypedMemSubPrefPtrs mem x2' t2' l2 stl1" using i2def f2 by simp
          moreover have "CompMemJustType (MTArray x1' t1') (MTArray x2 (MTArray x2' t2'))" using MTArray
            by (metis CompMemType_imps_CompMemJustType CompMemJustType.simps(2) CompMemType.simps(2))
          moreover have "MCon (MTArray x1' t1') mem l1"
            using a30 i1def by fastforce
          moreover have "CompMemType mem x1' t1' (MTArray x2 (MTArray x2' t2')) l1 stl2"
            by (meson CompMemType_asc_withSharedTarget CompTypeRemainsMCon MTArray.prems(4) MTArray.prems(6) calculation(1) i1def CompMemType.simps(2))
          ultimately have "\<not> TypedMemSubPrefPtrs mem x2 (MTArray x2' t2') stl2 l1"
            using MTArray(1)[of x1' l1] * False
            using MConSubTypes MTArray.prems(4) CompMemJustType.simps(2) MTArray(6)
            by (metis BothMConImpsNotCompMemType CompMemType_asc_withSharedTarget compMemTypes_trns i1def CompMemType.simps(2))
          then show ?thesis using * False f2
            using MConSubTypes MTArray.prems(4) CompMemJustType.simps(2)
            by (meson CompMemType_imps_CompMemJustType CompMemType_imps_TypedMemSubPrefPtrs CompTypeRemainsMCon MTArray.prems(1) MTArray.prems(6) compMemTypes_trns i2def CompMemType.simps(2))
        qed
      qed
    qed

  next
    case (MTValue x)
    then show ?case by fastforce
  qed
next
  case (MTValue x)
  then show ?case
  proof(induction t1 arbitrary:x1 stl1)
    case (MTArray x1 t1)
    then show ?case
      by fastforce
  next
    case (MTValue x)
    then show ?case by fastforce
  qed

qed

lemma TypedMemSubPrefPtrs_imps_notsame:
  assumes "TypedMemSubPrefPtrs m len'' arr'' stl1 prnt"
    and "MCon (MTArray len'' arr'') m stl1"
  shows "stl1 \<noteq> prnt" using assms
proof(induction arr'' arbitrary:len'' stl1)
  case (MTArray x1 arr'')
  obtain i l where iDef:"i<len'' \<and> accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some (MPointer l) \<and> (l = prnt \<or> TypedMemSubPrefPtrs m x1 arr'' l prnt)"
    using MTArray.prems(1) unfolding TypedMemSubPrefPtrs.simps by blast
  then have mc:"MCon (MTArray x1 arr'') m l" using MTArray.prems(2)
    using MCon_imps_sub_Mcon by blast
  then show ?case
  proof(cases "l= prnt")
    case True
    then show ?thesis using iDef mc
      using MConPtrsMustBeSubLocs MTArray.prems(2) by blast
  next
    case False
    then show ?thesis using MTArray.IH iDef mc
      by (metis CompMemType_imps_CompMemJustType CompMemType_imps_TypedMemSubPrefPtrs MTArray.prems(2) TypedMemSubPrefOneWay CompMemType.simps(2))
  qed
next
  case (MTValue x)
  then show ?case by force
qed

lemma existingLocation_imps_allLocs:
  assumes "CompMemType m len (MTArray len' arr') subT prnt stl1"
    and "MCon (MTArray len (MTArray len' arr')) m prnt"
  shows "\<forall>i<len. \<forall>l. accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some (MPointer l) \<and> l\<noteq>stl1 \<and> TypedMemSubPrefPtrs m len' arr' l stl1
\<longrightarrow> CompMemType m len' arr' subT l stl1"
proof intros
  fix i l
  assume asm1:"i < len"
    and asm2:"accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some (MPointer l) \<and> l \<noteq> stl1 \<and> TypedMemSubPrefPtrs m len' arr' l stl1"
  show "CompMemType m len' arr' subT l stl1" using assms asm2 asm1
  proof(induction arr' arbitrary:len' l)
    case (MTArray x1 arr')
    then show ?case
      by (meson CompMemType_asc_withSharedTarget CompTypeRemainsMCon CompMemType.simps(2))
  next
    case (MTValue x)
    then show ?case
      by (meson CompMemType_asc_withSharedTarget CompTypeRemainsMCon CompMemType.simps(2))
  qed
qed


lemma existingLocation_imps_allLocs_same:
  assumes "CompMemType m len t subT prnt stl1"
    and "MCon (MTArray len t) m prnt"
  shows "\<forall>i<len. \<forall>l. accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some (MPointer l) \<and> l =stl1
\<longrightarrow> subT = t"
proof intros
  fix i l
  assume asm1:"i < len"
    and asm2:"accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m = Some (MPointer l) \<and> l = stl1 "
  show "subT = t" using assms asm2 asm1
  proof(induction t arbitrary:len l)
    case (MTArray x1 arr')

    obtain i'' ptr where ptrDef:"(i''<len \<and> accessStore (hash prnt (ShowL\<^sub>n\<^sub>a\<^sub>t i'')) m = Some (MPointer ptr)
                                  \<and> (ptr = stl1 \<and> MTArray x1 arr' = subT
                                      \<or> CompMemType m x1 arr' subT ptr stl1))"
      using MTArray.prems(1) unfolding CompMemType.simps(2) by blast
    then show ?case
    proof(cases "ptr = l")
      case True
      then show ?thesis
        using BothMConImpsNotCompMemType CompTypeRemainsMCon MCon_imps_sub_Mcon MTArray.prems(2,3) ptrDef by blast
    next
      case False
      then have "CompMemType m x1 arr' subT ptr stl1" using ptrDef
        by (simp add: MTArray.prems(3))
      then show ?thesis using ptrDef False
        using CompMemTypeSameLocsSameType MTArray.prems(2,3,4) CompMemType.simps(2) by blast
    qed

  next
    case (MTValue x)
    then show ?case by simp
  qed
qed

lemma CompMemType_imps_in_GetAllMemoryLocations_ptr:
  assumes "MCon (MTArray len2 arr2) mem stl2"
    and "CompMemType mem len2 arr2 (MTArray len3 arr3) stl2 locs"
  shows "\<forall>i<len3. hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<in> GetAllMemoryLocations (MTArray len2 arr2) stl2 mem" using assms
proof (induction arr2 arbitrary: len2 stl2)
  case (MTArray x11 x12)
  have "(\<exists>i<len2.
        \<exists>l. accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l)
        \<and> (l = locs \<and> MTArray x11 x12 = MTArray len3 arr3 \<or> CompMemType mem x11 x12 (MTArray len3 arr3) l locs))"
    using MTArray.prems(2) CompMemType.simps(2)[of mem len2 x11 x12 "(MTArray len3 arr3)" stl2 locs] by blast
  then obtain i l where iDef:"i<len2 \<and> accessStore (hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer l)
              \<and> (l = locs \<and> MTArray x11 x12 = MTArray len3 arr3 \<or> CompMemType mem x11 x12 (MTArray len3 arr3) l locs)" by blast
  then have mc:"MCon (MTArray x11 x12) mem l" using MTArray.prems(1)
    using MCon_imps_sub_Mcon by blast
  then show ?case
  proof(cases "l = locs")
    case True
    then have st:"MTArray x11 x12 = MTArray len3 arr3" using iDef
      using MTArray.prems(1,2) existingLocation_imps_allLocs_same by blast
    then have "\<forall>i''<len3. hash l (ShowL\<^sub>n\<^sub>a\<^sub>t i'') \<in> {hash stl2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)} \<union> GetAllMemoryLocations (MTArray len3 arr3) l mem"
      using GetAllMemoryLocations_Arry_Contains_Indexs[OF mc] by blast
    then show ?thesis using GetAllMemoryLocations.simps(2)[of len2 "MTArray len3 arr3" stl2 mem] st True iDef by force
  next
    case False
    then have "CompMemType mem x11 x12 (MTArray len3 arr3) l locs" using iDef by simp
    then have "\<forall>i<len3. hash locs (ShowL\<^sub>n\<^sub>a\<^sub>t i) \<in> GetAllMemoryLocations (MTArray x11 x12) l mem"
      using MTArray.IH[OF mc] by blast
    then show ?thesis using GetAllMemoryLocations.simps(2)[of len2 "MTArray x11 x12" stl2 mem] iDef by force
  qed
next
  case (MTValue x2)
  then show ?case using MTValue by auto
qed


lemma typedPrefix_imp_SubPref:
  shows "TypedMemSubPref child parent t \<longrightarrow> LSubPrefL2 child parent"
proof(induction t arbitrary:parent)
  case (MTArray x1 t)
  show ?case
  proof intros
    assume *:"TypedMemSubPref child parent (MTArray x1 t)"
    then have **:"(\<exists>i<x1. TypedMemSubPref child (hash parent (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t \<or> child = (hash parent (ShowL\<^sub>n\<^sub>a\<^sub>t i)))"
      using TypedMemSubPref.simps(2)[of child parent x1 t] by auto
    then show "LSubPrefL2 child parent"
    proof(cases "\<exists>i<x1. child = (hash parent (ShowL\<^sub>n\<^sub>a\<^sub>t i))")
      case True
      then show ?thesis unfolding LSubPrefL2_def by auto
    next
      case False
      then obtain i where "i < x1 \<and> TypedMemSubPref child (hash parent (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t" using ** by auto
      then have "LSubPrefL2 child (hash parent (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using MTArray by auto

      then show "LSubPrefL2 child parent" unfolding LSubPrefL2_def
        using LSubPrefL2_def Not_Sub_More_Specific by blast
    qed

  qed
next
  case (MTValue x)
  then show ?case
  proof intros
    assume "TypedMemSubPref child parent (MTValue x)"
    then show "LSubPrefL2 child parent" unfolding LSubPrefL2_def by auto
  qed
qed

text \<open>Locations inside element \<open>i < x\<close> of an array are never below index \<open>x\<close>.\<close>

lemma TypedMemSubPref_not_below_index:
  assumes "TypedMemSubPref l p (MTArray x t)"
    and "LSubPrefL2 l' l"
  shows "\<not> LSubPrefL2 l' (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t x))"
proof
  assume below: "LSubPrefL2 l' (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t x))"
  obtain i where i: "i < x" "TypedMemSubPref l (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)) t \<or> l = hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i)"
    using assms(1) by auto
  then have "LSubPrefL2 l (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i))"
    using typedPrefix_imp_SubPref LSubPrefL2_refl by blast
  then have "LSubPrefL2 l' (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t i))"
    using assms(2) unfolding LSubPrefL2_def by (metis hash_suffixes_associative)
  then have "i = x" using below LSubPrefL2_index_unique by blast
  then show False using i(1) by simp
qed

corollary TypedMemSubPref_index_disjoint:
  "TypedMemSubPref l p (MTArray x t) \<Longrightarrow> \<not> LSubPrefL2 l (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t x))"
  using TypedMemSubPref_not_below_index LSubPrefL2_refl by blast

corollary TypedMemSubPref_index_disjoint_typed:
  "TypedMemSubPref l p (MTArray x t) \<Longrightarrow> \<not> TypedMemSubPref l (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t'"
  using TypedMemSubPref_index_disjoint typedPrefix_imp_SubPref by blast

corollary TypedMemSubPref_hash_not_below_index:
  "TypedMemSubPref l p (MTArray x t) \<Longrightarrow> \<not> LSubPrefL2 (hash l k) (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t x))"
  using TypedMemSubPref_not_below_index LSubPrefL2_hash by blast

corollary TypedMemSubPref_hash_index_disjoint_typed:
  "TypedMemSubPref l p (MTArray x t) \<Longrightarrow> \<not> TypedMemSubPref (hash l k) (hash p (ShowL\<^sub>n\<^sub>a\<^sub>t x)) t'"
  using TypedMemSubPref_not_below_index LSubPrefL2_hash typedPrefix_imp_SubPref by blast


lemma CompMemTypeSubTypes_neg:
  shows "\<not>CompMemType v' x1 t (MTArray x1 t) l destl'"
proof
  assume "CompMemType v' x1 t (MTArray x1 t) l destl'"
  then have a1:"CompMemType v' x1 t (MTArray x1 t) l destl'" by simp
  show False using a1
  proof(induction t arbitrary:x1 l)
    case (MTArray x11 x12)
    then show ?thesis unfolding CompMemType.simps
      by (metis CompMemJustType.simps(2) CompMemType_imps_CompMemJustType MTArray.prems mtypes.inject(1)
          reversible_CompMemJustType_imps_same)
  next
    case (MTValue x2)
    then show ?thesis by simp
  qed
qed


lemma CompMemType_imps_Mid:
  assumes "CompMemType mem len arr (MTArray x11 x12) pParentPtr p"
  shows "arr = MTArray x11 x12 \<and> (\<exists>i<len. accessStore (hash pParentPtr (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer p))
       \<or> (\<exists>midP subL subA i.
            CompMemType mem len arr (MTArray subL subA) pParentPtr midP
            \<and> accessStore (hash midP (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some (MPointer p)
            \<and> i < subL
            \<and> subA = MTArray x11 x12)"
  using assms
proof(induction arr arbitrary:len pParentPtr)
  case (MTArray x1 arr)
  obtain ii ll where iiDef:"ii<len \<and> accessStore (hash pParentPtr (ShowL\<^sub>n\<^sub>a\<^sub>t ii)) mem = Some (MPointer ll) \<and>
(ll = p \<and> MTArray x1 arr = MTArray x11 x12 \<or> CompMemType mem x1 arr (MTArray x11 x12) ll p)"
    using MTArray.prems unfolding CompMemType.simps by blast
  then show ?case
  proof(cases "MTArray x1 arr = MTArray x11 x12")
    case True
    then have "ll = p" using iiDef
      using CompMemTypeSubTypes_neg by blast
    then show ?thesis using iiDef True by blast
  next
    case False
    then have comp: "CompMemType mem x1 arr (MTArray x11 x12) ll p" using iiDef by blast
    then show ?thesis using MTArray.IH[of x1 ll] iiDef by fastforce
  qed
next
  case (MTValue x)
  then show ?case unfolding CompMemType.simps by simp
qed


subsection \<open>Locations above the top location\<close>

lemma AllPtrsNotTop_MCon:
  assumes "lessThanTopLocs mem"
  shows "\<forall>tl. tl \<ge> Toploc mem \<and> MCon t mem ptr\<longrightarrow>
        (\<not>LSubPrefL2 ptr (ShowL\<^sub>n\<^sub>a\<^sub>t tl))\<and>
        (\<not>LSubPrefL2 (ShowL\<^sub>n\<^sub>a\<^sub>t tl) ptr)"
proof intros
  fix tl
  assume *:" Toploc mem \<le> tl \<and> MCon t mem ptr"
  then have ptrMCon:"MCon t mem ptr" by force
  have SomeA:"\<exists>x i. accessStore ptr mem = Some x \<or> accessStore (hash ptr (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem = Some x"
    using MCon_imps_Some[OF ptrMCon] by blast
  have toplocs:"lessThanTopLocs mem" using assms(1) by blast
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


lemma lessThanTop_topChange_MCon:
  assumes "\<forall>locs. \<not> LSubPrefL2 locs (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo)) \<or> locs = (ShowL\<^sub>n\<^sub>a\<^sub>t
      (Toploc mo)) \<longrightarrow> accessStore locs mo = accessStore locs m"
    and "MCon tp mo x2"
    and "\<not> LSubPrefL2 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo)) x2 \<and> \<not> LSubPrefL2 x2 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo))"
    and "lessThanTopLocs mo"
  shows " MCon tp (m) x2" using assms(2,3)
proof(induction tp arbitrary:x2)
  case (MTArray x1 tp)
  then have old:"0 < x1 \<and> (\<forall>i<x1.
    case accessStore (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mo of None \<Rightarrow> False | Some (MValue val) \<Rightarrow>
(case tp of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon tp mo (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
| Some (MPointer loc2) \<Rightarrow> (case tp of MTArray len' arr' \<Rightarrow> MCon tp mo loc2 | MTValue val \<Rightarrow> False)) \<and>
(\<exists>p. accessStore x2 mo = Some (MPointer p) \<or> accessStore x2 mo = None)"
    unfolding MCon.simps by simp
  then have "(\<exists>p. accessStore x2 m = Some (MPointer p) \<or> accessStore x2 m = None)"
    using assms(1) MTArray.prems(2) by auto
  moreover have "(\<forall>i<x1.
    case accessStore (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m of None \<Rightarrow> False | Some (MValue val) \<Rightarrow>
(case tp of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon tp m (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
| Some (MPointer loc2) \<Rightarrow> (case tp of MTArray len' arr' \<Rightarrow> MCon tp m loc2 | MTValue val \<Rightarrow> False))"
  proof intros
    fix i
    assume in1:"i<x1"
    then have sameAcc:"accessStore (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mo = accessStore (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m"
      using MTArray.prems(2) assms(1)
      using Mutual_NonSub_SpecificNonSub by presburger
    show " case accessStore (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m of None \<Rightarrow> False | Some (MValue val) \<Rightarrow>
(case tp of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon tp m (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
| Some (MPointer loc2) \<Rightarrow> (case tp of MTArray len' arr' \<Rightarrow> MCon tp m loc2 | MTValue val \<Rightarrow> False)"
    proof(cases "accessStore (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mo")
      case None
      then show ?thesis using sameAcc old in1 by auto
    next
      case (Some a)
      then show ?thesis
      proof(cases a)
        case (MValue x1')
        then have "MCon tp mo (hash x2 (ShowL\<^sub>n\<^sub>a\<^sub>t i))"
          using sameAcc old in1 Some
          using MCon_imps_sub_Mcon MTArray.prems(1) by blast
        moreover have "\<exists>v. tp = MTValue v" using calculation Some MValue by (cases tp, simp+)
        ultimately show ?thesis using sameAcc Some MValue
          by (metis MTArray.IH MTArray.prems(2) mtypes.simps(6) MemLSubPrefL2_specific_imps_general memoryvalue.simps(5) Option.option.simps(5) Not_Sub_More_Specific)
      next
        case (MPointer x2')
        then have mcOld:"MCon tp mo x2'" using old Some in1 by (cases tp, auto)

        moreover have "\<not> LSubPrefL2 (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo)) x2' \<and> \<not> LSubPrefL2 x2' (ShowL\<^sub>n\<^sub>a\<^sub>t (Toploc mo))"
          using AllPtrsNotTop_MCon calculation assms(4) by (meson le_refl)
        ultimately have "MCon tp m x2'" using MTArray.IH[of x2'] by simp
        moreover have "\<exists>l a. tp = MTArray l a" using Some MPointer old
          by (metis MTArray.prems(1) memoryvalue.distinct(1) in1 mcon_accessStore option.inject)
        ultimately show ?thesis using in1 sameAcc Some MPointer
          by (metis mtypes.simps(5) memoryvalue.simps(6) Option.option.simps(5))
      qed
    qed
  qed
  moreover have "0 < x1" using old by simp
  ultimately show ?case unfolding MCon.simps by simp
next
  case (MTValue x)
  then show ?case using assms(1) by auto
qed


lemma MCon_memory_transfer:
  assumes "MCon t mem_old ptr_loc"
    and "\<not> LSubPrefL2 ptr_loc toploc_new \<and> \<not> LSubPrefL2 toploc_new ptr_loc"
    and "\<forall>len arr loc. t = MTArray len arr \<and> TypedMemSubPrefPtrs mem_old len arr ptr_loc loc
         \<longrightarrow> \<not> LSubPrefL2 loc toploc_new \<and> \<not> LSubPrefL2 toploc_new loc"
    and "\<forall>loc. \<not> LSubPrefL2 loc toploc_new \<or> loc = toploc_new
         \<longrightarrow> accessStore loc mem_new = accessStore loc mem_old"
  shows "MCon t mem_new ptr_loc"
  using assms(1,2,3)
proof(induction t arbitrary:ptr_loc)
  case (MTArray x1 struct)
  have "x1 > 0" using MTArray.prems(1) unfolding MCon.simps
    using bot_nat_0.not_eq_extremum by fastforce
  moreover have "(\<exists>p. accessStore ptr_loc mem_new = Some (MPointer p)) \<or> accessStore ptr_loc mem_new = None"
    using MTArray.prems(1,2) unfolding MCon.simps using assms(3,4) calculation(1) by simp
  moreover have "\<forall>i<x1.
    (case accessStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem_new of None \<Rightarrow> False
     | Some (MValue val) \<Rightarrow> (case struct of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon struct mem_new (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
     | Some (MPointer loc2) \<Rightarrow> (case struct of MTArray len' arr' \<Rightarrow> MCon struct mem_new loc2 | MTValue val \<Rightarrow> False))"
  proof intros
    fix i
    assume *:"i<x1"
    then have notSub:"\<not> LSubPrefL2 (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) toploc_new \<or> (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) = toploc_new"
      using MTArray.prems(2) Mutual_NonSub_SpecificNonSub by auto
    show "(case accessStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem_new of None \<Rightarrow> False
     | Some (MValue val) \<Rightarrow> (case struct of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon struct mem_new (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
     | Some (MPointer loc2) \<Rightarrow> (case struct of MTArray len' arr' \<Rightarrow> MCon struct mem_new loc2 | MTValue val \<Rightarrow> False))"
    proof(cases struct)
      case (MTArray x11' x12')
      obtain loc2 where loc2Def:"accessStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem_old = Some (MPointer loc2)
                        \<and> MCon struct mem_old loc2"
        using MTArray.prems(1) *
        by (metis MConArrayPointers MCon_imps_sub_Mcon MTArray calculation(1))
      then have o1:"\<forall>loc. TypedMemSubPrefPtrs mem_old x1 struct ptr_loc loc \<longrightarrow>
                 \<not> LSubPrefL2 loc toploc_new \<and> \<not> LSubPrefL2 toploc_new loc"
        using MTArray.prems by simp
      have "\<forall>len arr loc. struct = MTArray len arr \<and> TypedMemSubPrefPtrs mem_old len arr loc2 loc \<longrightarrow>
            \<not> LSubPrefL2 loc toploc_new \<and> \<not> LSubPrefL2 toploc_new loc"
        using o1 loc2Def * by fastforce
      moreover have "TypedMemSubPrefPtrs mem_old x1 struct ptr_loc loc2"
        using o1 loc2Def *
        using MTArray TypedMemSubPrefPtrs.simps(2) by blast
      moreover have "\<not> LSubPrefL2 loc2 toploc_new \<and> \<not> LSubPrefL2 toploc_new loc2"
        using o1 calculation assms by simp
      ultimately have "MCon struct mem_new loc2" using MTArray.IH[of loc2] loc2Def by simp
      moreover have "accessStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem_new = Some (MPointer loc2) "
        using loc2Def * notSub assms(4) by simp
      ultimately show ?thesis
        using MTArray by force
    next
      case (MTValue x2)
      then obtain v where vDef:"accessStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem_old = Some (MValue v)
                            \<and> MCon (MTValue x2) mem_old (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i))"
        using * MTArray.prems(1)
        by (meson MCon_imps_sub_Mcon MCon_sub_MTVal_imps_val)
      then have "accessStore (hash ptr_loc (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem_new = Some (MValue v)"
        using notSub assms(4) by simp
      then show ?thesis using vDef MTValue unfolding MCon.simps
        using notSub assms(4) by fastforce
    qed
  qed
  ultimately show ?case unfolding MCon.simps by simp
next
  case (MTValue x)
  then show ?case using assms(4) unfolding MCon.simps by simp
qed


subsection \<open>Preservation of type relations by copying\<close>

lemma cpm2mCompMemTypeOld_imps_CompMemType:
  assumes " CompMemType mem' len x tp2 stl1 stl2"
    and "\<forall>locs. \<not> LSubPrefL2 locs l \<longrightarrow> accessStore locs mem' = accessStore locs m'"
    and "\<not> LSubPrefL2 stl1 l"
    and "\<forall>loc. LSubPrefL2 loc l \<longrightarrow> accessStore loc mem' = None"
    and "MCon (MTArray len x) mem' stl1"
  shows " CompMemType m' len x tp2 stl1 stl2" using assms
proof(induction x arbitrary:stl1 len)
  case (MTArray x1 tp1)
  have c10:"(\<exists>i<len. \<exists>l. accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem' = Some (MPointer l)
            \<and> ((l = stl2) \<and> MTArray x1 tp1 = tp2 \<or> CompMemType mem' x1 tp1 tp2 l stl2))"
    using MTArray(2) CompMemType.simps(2)[of mem' len x1 tp1 tp2 stl1 stl2] using hash_inequality by auto
  then obtain i l' where idef:"i<len \<and> accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem' = Some (MPointer l') \<and> ((l'
      = stl2 ) \<and> MTArray x1 tp1 = tp2 \<or> CompMemType mem' x1 tp1 tp2 l' stl2)"
    using c10 by auto
  then have c20:"accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some (MPointer l')" using MTArray(3, 4) LSubPrefL2_def
    by (metis MTArray(3,5) not_None_eq)
  have "\<forall>i<len.
           (case accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem' of None \<Rightarrow> False
            | Some (MValue val) \<Rightarrow> (case MTArray x1 tp1 of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon
                (MTArray x1 tp1) mem' (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
            | Some (MPointer loc2) \<Rightarrow> (case MTArray x1 tp1 of MTArray len' arr' \<Rightarrow> MCon (MTArray x1 tp1) mem' loc2 | MTValue Types \<Rightarrow> False)) \<and>
           ((\<exists>p. accessStore stl1 mem' = Some (MPointer p)) \<or> accessStore stl1 mem' = None)"
    using MTArray(6) MCon.simps(2)[of len "(MTArray x1 tp1)" mem' stl1] by auto
  then have mcond:"MCon (MTArray x1 tp1) mem' l'" using MTArray(6) using idef c10
    by (metis (no_types, lifting) mtypes.simps(5) memoryvalue.simps(6) Option.option.simps(5))
  have "\<not> LSubPrefL2 l' l"
    by (metis MCon_imps_Some LSubPrefL2_def assms(4) Not_Sub_More_Specific mcond not_None_eq)
  then have "CompMemType mem' x1 tp1 tp2 l' stl2 \<longrightarrow> CompMemType m' x1 tp1 tp2 l' stl2"
    using MTArray(1)[of x1 l'] MTArray(3,5) mcond by auto

  moreover have "((l' = stl2) \<and> MTArray x1 tp1 = tp2 \<or> CompMemType mem' x1 tp1 tp2 l' stl2)" using c10 idef by simp
  ultimately have "(l' = stl2) \<and> MTArray x1 tp1 = tp2 \<or> CompMemType m' x1 tp1 tp2 l' stl2" using MTArray(1) MTArray(3,5) mcond by auto

  then show ?case using idef c10 c20
    using MTArray.prems(1) by auto
next
  case (MTValue x)
  then show ?case using TypedMemSubPrefPtrs.simps(1) by auto
qed

lemma inv_cpm2mTPrefOld_imps_TPref:
  assumes "\<not>TypedMemSubPrefPtrs mem' len x stl1 stl2"
    and "\<forall>locs. \<not> LSubPrefL2 locs l \<longrightarrow> accessStore locs mem' = accessStore locs m'"
    and "\<not> LSubPrefL2 stl1 l"
    and "\<forall>loc. LSubPrefL2 loc l \<longrightarrow> accessStore loc mem' = None"
    and "MCon (MTArray len x) mem' stl1"
  shows "\<not>TypedMemSubPrefPtrs m' len x stl1 stl2" using assms
proof(induction x arbitrary:stl1 len)
  case (MTArray x1 tp1)
  show ?case
  proof
    assume *:"TypedMemSubPrefPtrs m' len (MTArray x1 tp1) stl1 stl2"
    then have a10:"(\<exists>i<len. \<exists>l. accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some (MPointer l) \<and> (l = stl2 \<or> TypedMemSubPrefPtrs m' x1 tp1 l stl2))"
      using TypedMemSubPrefPtrs.simps(2)[of m' len x1 tp1 stl1 stl2] by blast
    have a20:"(\<forall>i<len. \<not>(\<exists>l. accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem' = Some (MPointer l) \<and>
        (l = stl2 \<or> TypedMemSubPrefPtrs mem' x1 tp1 l stl2)))" using MTArray(2) * by auto

    then obtain i l' where idef:"i<len \<and> accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) m' = Some (MPointer l') \<and> (l' =
        stl2 \<or> TypedMemSubPrefPtrs m' x1 tp1 l' stl2)" using a10 by auto
    then have c20:"accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem' = Some (MPointer l')" using MTArray(3, 4) LSubPrefL2_def
      by (metis MConArrayPointers MTArray.prems(5) a10 assms(4) gr_zeroI less_nat_zero_code option.discI)

    have "\<forall>i<len.
             (case accessStore (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)) mem' of None \<Rightarrow> False
              | Some (MValue val) \<Rightarrow> (case MTArray x1 tp1 of MTArray l a \<Rightarrow> False | MTValue typ \<Rightarrow> MCon
                  (MTArray x1 tp1) mem' (hash stl1 (ShowL\<^sub>n\<^sub>a\<^sub>t i)))
              | Some (MPointer loc2) \<Rightarrow> (case MTArray x1 tp1 of MTArray len' arr' \<Rightarrow> MCon (MTArray x1 tp1) mem' loc2 | MTValue Types \<Rightarrow> False))"
      using MTArray(6) MCon.simps(2)[of len "MTArray x1 tp1" mem' stl1] by auto
    then have c30:"MCon (MTArray x1 tp1) mem' l'" using MTArray(6) using idef c20
      by (metis (no_types, lifting) mtypes.simps(5) memoryvalue.simps(6) Option.option.simps(5))
    moreover have "\<not> LSubPrefL2 l' l" using MTArray(4,5) c20 idef c30
      by (metis MCon_imps_Some LSubPrefL2_def Not_Sub_More_Specific not_None_eq)
    ultimately show False using MTArray
      using a20 c20 idef by auto
  qed
next
  case (MTValue x)
  then show ?case by simp
qed


lemma selfPoint_imps_TypedMemSubPref:
  assumes "\<forall>l l'. TypedMemSubPref l ld (MTArray x t) \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l"
    and "TypedMemSubPrefPtrs v' x t ld x3"
  shows "TypedMemSubPref x3 ld (MTArray x t)" using assms(1,2)
proof(induction t arbitrary:ld x)
  case (MTArray x1 t)
  then have "\<exists>i<x. \<exists>l. accessStore (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = Some (MPointer l) \<and> (l = x3 \<or> TypedMemSubPrefPtrs v' x1 t l x3)"
    using TypedMemSubPrefPtrs.simps(2)[of v' x x1 t ld x3] by blast
  then obtain i l where idef:"i<x \<and> accessStore (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = Some (MPointer l) \<and> (l = x3 \<or> TypedMemSubPrefPtrs v' x1 t l x3)" by blast
  then have ldef:"l = (hash ld (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using MTArray(2)
    by (metis TypedMemSubPref.simps(2))
  then show ?case
  proof(cases "x3 = l")
    case True
    then show ?thesis using ldef idef by auto
  next
    case False
    have "\<forall>la l'. TypedMemSubPref la l (MTArray x1 t) \<and> accessStore la v' = Some (MPointer l') \<longrightarrow> l' = la" using ldef idef MTArray.prems(1)
      using moreSpecificTypedSubPref by blast
    then have "(TypedMemSubPref x3 l (MTArray x1 t))" using MTArray.IH[of l x1] idef False by blast
    then show ?thesis using TypedMemSubPref.simps(2)[of x3 ld x "MTArray x1 t"] using ldef idef by blast
  qed
next
  case (MTValue x)
  then show ?case by auto
qed

lemma CompMemType_preservation_induction:
  assumes store_preserved: "\<forall>locs. \<not> LSubPrefL2 locs hash_loc \<longrightarrow> accessStore locs v' = accessStore locs v''"
    and no_prefix_conflict: "\<forall>l. TypedMemSubPref l destl (MTArray x t) \<longrightarrow> \<not> LSubPrefL2 l hash_loc"
    and store_consistency: "\<forall>l. TypedMemSubPref l destl (MTArray x t) \<longrightarrow> accessStore l v' = accessStore l v''"
    and type_exists: "CompMemType v' x t (MTArray x11 x12) destl destl' \<and> (\<forall>i<x11. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = Some x12)"
    and self_pointers: "\<forall>l l'. TypedMemSubPref l destl (MTArray x t) \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l"
    and type_preserved: "\<forall>i<x11. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v''"
  shows "CompMemType v'' x t (MTArray x11 x12) destl destl' \<and> (\<forall>i<x11. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' = Some x12)"
  using assms(1,2,3,4,5)
proof(induction t arbitrary: x destl)
  case (MTArray x1 t)
  obtain i l where idef:"i<x \<and> accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = Some (MPointer l) \<and>
                     (l = destl' \<and> MTArray x1 t = (MTArray x11 x12) \<or> CompMemType v' x1 t (MTArray x11 x12) l destl') \<and>
                        (\<forall>i<x11. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = Some x12)"
    using MTArray.prems unfolding CompMemType.simps by blast
  then have tps:"TypedMemSubPref (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) destl (MTArray x (MTArray x1 t))" by auto
  then have self:"l = (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using idef MTArray.prems by blast
  then have noSub:"\<not> LSubPrefL2 l hash_loc" using idef
    using MTArray.prems(2) tps by presburger
  have sameACC:" accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' = accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'" using assms(1) MTArray.prems(2) idef by auto
  then show ?case
  proof(cases "MTArray x1 t = (MTArray x11 x12)")
    case True
    then have "\<not>CompMemType v' x1 t (MTArray x11 x12) l destl'" using CompMemTypeSubTypes_neg by auto
    then have "l = destl'" using idef by simp
    moreover have "accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v''"
      using True tps self noSub MTArray.prems(3) by blast
    moreover have "\<forall>i<x1. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v''"
      using MTArray.prems(2) assms(6) True by simp
    ultimately show ?thesis using True idef self
      using MTArray.prems(3) tps by auto
  next
    case False
    then have "CompMemType v' x1 t (MTArray x11 x12) l destl'" using idef by auto
    then have cc0:"CompMemType v' x1 t (MTArray x11 x12) l destl' \<and>
                  (\<forall>i<x11. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = Some x12)"
      using idef by simp
    moreover have cc1:"\<forall>la. TypedMemSubPref la l (MTArray x1 t) \<longrightarrow> accessStore la v' = accessStore la v''"
      using MTArray.prems(3) Not_Sub_More_Specific_more_speific self idef tps by blast
    moreover have cc2:"\<forall>la l'. TypedMemSubPref la l (MTArray x1 t) \<and> accessStore la v' = Some (MPointer l') \<longrightarrow> l' = la"
      using MTArray.prems(5) tps self Not_Sub_More_Specific_more_speific idef by blast
    moreover have "\<forall>la. TypedMemSubPref la l (MTArray x1 t) \<longrightarrow> \<not> LSubPrefL2 la hash_loc" using self idef MTArray.prems(2) by auto
    ultimately have cc9:"CompMemType v'' x1 t (MTArray x11 x12) l destl' \<and> (\<forall>i<x11. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' = Some x12)"
      using MTArray.IH[OF assms(1) _ cc1 cc0 cc2] noSub self by blast
    then show ?thesis using cc9 idef self sameACC unfolding CompMemType.simps by auto
  qed
next
  case (MTValue x')
  have a0:"CompMemType v' x (MTValue x') (MTArray x11 x12) destl destl'"
    using MTValue by blast
  then show ?case using a0 unfolding CompMemType.simps by simp

qed


lemma CompMemTypeValue_preservation_induction:
  assumes store_preserved: "\<forall>locs. \<not> LSubPrefL2 locs hash_loc \<longrightarrow> accessStore locs v' = accessStore locs v''"
    and no_prefix_conflict: "\<forall>l. TypedMemSubPref l destl (MTArray x t) \<longrightarrow> \<not> LSubPrefL2 l hash_loc"
    and store_consistency: "\<forall>l. TypedMemSubPref l destl (MTArray x t) \<longrightarrow> accessStore l v' = accessStore l v''"
    and type_exists: "accessTypeStore destl' v' = Some (MTValue ttt) \<and> CompMemType v' x t (MTValue ttt) destl destl'"
    and self_pointers: "\<forall>l l'. TypedMemSubPref l destl (MTArray x t) \<and> accessStore l v' = Some (MPointer l') \<longrightarrow> l' = l"
    and type_preserved: "accessTypeStore destl' v' = accessTypeStore destl' v''"
  shows "CompMemType v'' x t (MTValue ttt) destl destl' \<and> accessTypeStore destl' v'' = Some (MTValue ttt)"
  using assms(1,2,3,4,5)
proof(induction t arbitrary: x destl)
  case (MTArray x1 t)
  obtain i l where idef:"accessTypeStore destl' v' = Some (MTValue ttt) \<and> i<x \<and> accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v' = Some (MPointer l) \<and>
                     (l = destl' \<and> MTArray x1 t = (MTValue ttt) \<or> CompMemType v' x1 t (MTValue ttt) l destl')"
    using MTArray.prems(4) unfolding CompMemType.simps by blast
  then have tps:"TypedMemSubPref (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) destl (MTArray x (MTArray x1 t))" by auto
  then have self:"l = (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i))" using idef MTArray.prems(5) by blast
  then have noSub:"\<not> LSubPrefL2 l hash_loc" using idef
    using MTArray.prems(2) tps by presburger
  have sameACC:" accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' = accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'" using assms(1) MTArray.prems(2) idef by auto

  then have "CompMemType v' x1 t (MTValue ttt) l destl'" using idef by simp
  then have cc0:" accessTypeStore destl' v' = Some (MTValue ttt) \<and> CompMemType v' x1 t (MTValue ttt) l destl'" using idef by blast
  moreover have cc1:"\<forall>la. TypedMemSubPref la l (MTArray x1 t) \<longrightarrow> accessStore la v' = accessStore la v''"
    using MTArray.prems(3) Not_Sub_More_Specific_more_speific self idef tps by blast
  moreover have cc2:"\<forall>la l'. TypedMemSubPref la l (MTArray x1 t) \<and> accessStore la v' = Some (MPointer l') \<longrightarrow> l' = la"
    using MTArray.prems(5) tps self Not_Sub_More_Specific_more_speific idef by blast
  moreover have "\<forall>la. TypedMemSubPref la l (MTArray x1 t) \<longrightarrow> \<not> LSubPrefL2 la hash_loc" using self idef MTArray.prems(2) by auto
  ultimately have cc9:"CompMemType v'' x1 t (MTValue ttt) l destl' \<and> accessTypeStore destl' v'' = Some (MTValue ttt)"
    using MTArray.IH[OF assms(1) _ cc1 cc0 cc2] noSub self by blast
  then show ?case using cc9 idef self sameACC unfolding CompMemType.simps by auto
next
  case (MTValue x')
  have a0:"accessTypeStore destl' v' = Some (MTValue ttt) \<and> CompMemType v' x (MTValue x') (MTValue ttt) destl destl'"
    using MTValue(4) by blast
  then have cc0:"accessTypeStore destl' v'' = Some (MTValue ttt)"
    using assms(6) by metis
  show ?case using a0 cc0 unfolding CompMemType.simps by simp
qed


lemma CompMemType_extend:
  assumes comp_exists: "\<exists>t''. CompMemType v'' x t t'' destl destl' \<and> accessTypeStore destl' v'' = Some t''"
  shows "\<exists>t''. CompMemType v'' (Suc x) t t'' destl destl' \<and> accessTypeStore destl' v'' = Some t''"
  using assms
proof(cases t)
  case (MTArray x11 x12)
  have cc:"\<exists>t''. \<exists>i< x.
 \<exists>l. accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' = Some (MPointer l) \<and>
     (l = destl' \<and> MTArray x11 x12 = t'' \<or> CompMemType v'' x11 x12 t'' l destl') \<and> accessTypeStore destl' v'' = Some t''"
    using assms MTArray by auto
  then have "\<exists>t''. CompMemType v'' (Suc x) (MTArray x11 x12) t'' destl destl'"
    unfolding CompMemType.simps
    using less_Suc_eq by blast
  then show ?thesis using MTArray cc
    using less_Suc_eq by auto
next
  case (MTValue x2)
  then show ?thesis using assms
    using less_Suc_eq by auto
qed

lemma CompMemType_extend_array:
  assumes comp_exists: "CompMemType v'' x t (MTArray x11' x12') destl destl'
                  \<and> (\<forall>i<x11'. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' = Some x12')"
  shows "CompMemType v'' (Suc x) t (MTArray x11' x12') destl destl'
                  \<and> (\<forall>i<x11'. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' = Some x12')"
  using assms
proof(cases t)
  case (MTArray x11 x12)
  then have "CompMemType v'' x (MTArray x11 x12) (MTArray x11' x12') destl destl'
              \<and> (\<forall>i<x11'. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' = Some x12')" using assms by simp
  then have cc:"(\<exists>i<x. \<exists>l. accessStore (hash destl (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' = Some (MPointer l) \<and>
             (l = destl' \<and> MTArray x11 x12 = MTArray x11' x12' \<or> CompMemType v'' x11 x12 (MTArray x11' x12') l destl')) \<and>
  (\<forall>i<x11'. accessTypeStore (hash destl' (ShowL\<^sub>n\<^sub>a\<^sub>t i)) v'' = Some x12')"
    unfolding CompMemType.simps by simp
  then have "\<exists>t''. CompMemType v'' (Suc x) (MTArray x11 x12) t'' destl destl'"
    unfolding CompMemType.simps
    using less_Suc_eq by blast
  then show ?thesis using MTArray cc
    using less_Suc_eq by auto
next
  case (MTValue x2)
  then show ?thesis using assms
    using less_Suc_eq by auto
qed

end
